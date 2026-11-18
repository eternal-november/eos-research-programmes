"""Same-history receiver comparison on the actual return-seat binary and raw capture ports."""
import argparse
from dataclasses import dataclass
from decimal import localcontext
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

import return_seat as seat
import rx_restoration as restoration
import native_clock_source as paced

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parent / "local-control"))
import receiver_model as receiver
import receiver_power_model as electrical

raw = seat.raw
need = seat.checks
D = restoration.DELTA
RATE = seat.parent.NATIVE_RATE
MASK = seat.parent.MASK
KINDS = ("fast_cmp", "fast_equal", "fast_range")
GROUP = 6976
DRIVER = 8192
CONTROL = 1120  # 928 plus a conservative 192 operations for the eleven physical timer bits


class FillTermination:
    """Physical 1024-capacity destination with a surplus shunt. Meter reads are audit data."""

    capacity = 1024

    def __init__(self, cell):
        self.cell = cell
        self.meter = Q(0)
        self.received = Q(0)
        self.shunt_heat = Q(0)

    @property
    def stock(self):
        # MeteredCell advances the fixed lead by writing its cumulative throughput.
        # Throughput is not another stored-energy account.
        return self.meter

    @stock.setter
    def stock(self, cumulative):
        incoming = Q(cumulative) - self.meter
        need(0 <= incoming <= 1024 - self.meter, "Invalid forward work")
        retained = min(incoming, self.cell.capacity - self.cell.stock)
        self.cell.stock += retained
        self.cell.received += retained
        self.shunt_heat += incoming - retained
        self.meter = cumulative


class RawRead:
    """One actual backend and role, one stock shared across its two source banks."""

    def __init__(self, lanes, role, voltage=200):
        self.lanes = {lane.identity.source_bank: lane for lane in lanes}
        self.cap = lanes[0].captures[role]
        for lane in lanes:
            ident = lane.identity
            need(lane.captures[role] is self.cap and lane.payer is self.cap.payer
                 and (ident.origin, ident.receiver, ident.receiver_bank) == self.cap.owner,
                 "Mixed raw owners or duplicate capture")
        self.role = role
        site = self.cap.owner[1:] if role == "primary" else (self.cap.owner[1], self.cap.owner[0])
        self.feeder = restoration.MeteredCell(restoration.power.catalogue()["capture"],
                                              (self.cap.owner, role), site, voltage)
        self.tee = FillTermination(self.cap.cell)
        self.feeder.capture_sink = self.tee
        self.claim = None
        self.left = Q(0)
        self.now = Q(0)
        self.requested = None
        self.stage = None
        self.due = None

    def flow(self, dt):
        need(dt >= 0 and (self.due is None or self.now + dt <= self.due), "Skipped raw boundary")
        if self.feeder.W >= restoration.D(self.feeder.s.capacitor * 100**2 / 2):
            self.feeder.unpowered(dt)
        else:
            self.feeder.low_unpowered(dt)
        if self.claim is not None:
            work = min(self.left, 1024 * dt / D)
            need(self.cap.cell.debit(work), "Raw read spent more than its own retained work")
            self.cap.cell.heat += work
            self.left -= work
        self.now += dt

    def request(self, bank, key):
        need(bank in self.lanes and key in self.lanes[bank].records
             and self.lanes[bank].records[key].role == self.role, "Wrong material target")
        if not self.cap.clock_enabled:
            return "stopped"
        if self.stage is not None:
            # There is no request queue. Each of the two physical banks uses
            # the same single raw cell, and the old itinerary is respected.
            return "busy"
        self.requested = (bank, key)
        self.new_fill()
        return "offered"

    def new_fill(self):
        if not self.cap.clock_enabled:
            self.requested = None
            return
        need(self.claim is None and (self.cap.pending is None or not self.cap.pending.live),
             "Prior raw capture was silently consumed")
        self.tee.meter = Q(0)  # per-grant integrator for the conservative verifier
        if self.feeder.reserve(2048, D, "capture-fill", sink=self.tee, net=1024):
            self.stage, self.due = "fill", self.now + D
        else:
            self.stage = self.due = self.requested = None

    def act(self):
        need(self.now == self.due and self.stage in ("fill", "read"), "Wrong raw strobe")
        if self.stage == "fill":
            bank, key = self.requested
            self.requested = self.stage = self.due = None
            if self.cap.clock_enabled and self.cap.cell.stock == 1024:
                lane = self.lanes[bank]
                before = lane.payer.stock
                need(self.cap.begin(lane, key) == "captured" and lane.payer.stock == before,
                     "Funded local read took remote work")
                self.claim, self.left = self.cap.pending, Q(1024)
                self.stage, self.due = "read", self.now + D
        else:
            claim = self.claim
            need(self.left == 0 and claim is self.cap.pending, "Unsettled or rebound raw work")
            def commit(bound, _):
                if self.cap.clock_enabled and not self.cap.control_dirty:
                    self.cap.snapshot = bound[0].read(bound[1])
            need(claim.dispatch(commit), "Duplicate raw read completion")
            self.cap.pending = self.claim = self.stage = self.due = None

    def install_live_old(self, bank, key):
        # Test entry at a real previous issuance with its full native work.
        # The new private CPU need not be running at that issuance.
        lane = self.lanes[bank]
        need(self.cap.cell.stock == 1024 and self.cap.pending is None
             and self.cap.begin(lane, key) == "captured", "No actual previous capture")
        self.claim, self.left = self.cap.pending, Q(1024)
        self.stage, self.due = "read", self.now + D


class ComparedParent(seat.charging.FramedParent):
    """The existing paid routed CPU. Timed comparisons use their own return strobe."""

    def complete(self, ports, *, native_ticks=None, clock=True, pause_after_offer=False):
        info = self._io_info()
        if info is None or info[0] not in KINDS:
            return super().complete(ports, native_ticks=native_ticks, clock=clock,
                                    pause_after_offer=pause_after_offer)
        if not clock or self.return_inhibit or self.committing:
            return "waiting"
        if not self.io_paid:
            if self.cell.stock < seat.parent.FRONT - self.pending.launch_work + GROUP + DRIVER:
                return "waiting"
            return super().complete(ports, clock=clock, pause_after_offer=True)
        op = self.child.physical_ports.operation
        if (not op.finished or self.fabric.token is not op.token or not op.token.live
                or self.pending is not op.captured or self.fabric.return_cut
                or op.socket.source is not self._body or op.socket.destination != info[1]):
            return "waiting"
        self.child.result = op.bit
        return super().complete(self.child.physical_ports, clock=clock)


@dataclass(frozen=True)
class Socket:
    source: object
    token: object
    captured: object
    destination: int


class PrivateOperation:
    def __init__(self, ports, name, args, machine):
        captured = machine.pending
        self.captured, self.token = captured, machine.fabric.token
        self.socket = Socket(captured.body, self.token, captured, machine.destination_latch)
        self.name, self.args, self.ports = name, args, ports
        self.start = ports.now
        self.endpoint = None
        self.descriptor = None
        self.ticks = 0  # observation of genuine edges
        self.delayline = [True] * 11  # earlier unqualified storage may be arbitrary
        self.value = self.bit = None
        self.finished = False
        self.stage = "select"
        self.due = self.start + (captured.launch_work + GROUP) / RATE
        self.raw_outcome = None

    def act(self):
        now = self.ports.now
        need(not self.finished and now == self.due, "No physical comparison boundary")
        if self.stage == "select":
            slot, bank, key = (a & MASK for a in self.args[:3])
            match, work = self.ports.selector.select(key, slot, bank)
            need(work == GROUP, "Unpriced group decode")
            if match is not None:
                origin, _, role = match
                self.endpoint = self.ports.endpoints[origin, role]
                need(self.endpoint.cap.owner == (origin, *self.ports.owner)
                     and self.endpoint.role == role, "Selected a foreign physical comparator")
            low = 0 if self.name == "fast_cmp" else self.args[3]
            self.descriptor = receiver.Descriptor(self.name, (match, key), low, self.args[-1],
                                                  self.socket.source, self.socket.destination)
            self.stage, self.due = "arm", now + D / 2
        elif self.stage == "arm":
            # The descriptor reaches its privately powered endpoint. No raw
            # receipt, idle bit or supply event participates in this arming.
            self.delayline[:] = [True] + [False] * 10
            self.stage, self.due = "timer", now + self.ports.first_edge
        elif self.stage == "timer":
            take_raw, take_private = self.delayline[5], self.delayline[10]
            self.delayline[:] = [False] + self.delayline[:-1]
            self.ticks += 1
            if take_raw:
                bank, key = self.args[1:3]
                if self.endpoint is not None:
                    self.endpoint.flow(now - self.endpoint.now)
                self.raw_outcome = "invalid" if self.endpoint is None else self.endpoint.request(bank, key)
            if not take_private:
                self.due = now + self.ports.periods[self.ticks - 1]
            else:
                self.value = MASK if self.endpoint is None else self.endpoint.cap.snapshot
                self.bit = receiver.predicate(self.descriptor, self.value)
                self.stage, self.due = "result", now + CONTROL / RATE + D / 2
        elif self.stage == "result":
            # Physical reset and the rest of this instruction's routed work
            # still have a duration. The already captured word is immutable.
            self.stage = "reset"
            self.due = now + D + (256 + seat.parent.FRONT - self.captured.launch_work) / RATE
        else:
            need(self.stage == "reset", "Unknown private phase")
            self.finished, self.due = True, None


class PrivatePorts:
    def __init__(self, owner, selector, endpoints, first_edge, periods):
        self.owner, self.selector, self.endpoints = owner, selector, endpoints
        self.first_edge, self.periods = Q(first_edge), tuple(map(Q, periods))
        lo, hi = D / 2, 101 * D / 200
        need(0 <= self.first_edge <= hi and len(self.periods) == 10
             and all(lo <= v <= hi for v in self.periods), "Outside the private clock envelope")
        self.now = Q(0)
        self.operation = None
        self.issues = 0

    def perform(self, name, args, cpu):
        need(name in KINDS and self.owner == cpu.bank.owner and len(args) == cpu.isa.PRIM_ARITY[name]
             and cpu.io_args is args and cpu.fabric.token.live and cpu.fabric.token.issued
             and (self.operation is None or self.operation.finished), "Unbound paid comparison")
        # RetirableParent already partitions the original 9184 from the same
        # 20480. Reserve the difference at this same material origin.
        need(cpu.cell.debit(GROUP + DRIVER - 9184), "Missing private power allowance")
        self.operation = PrivateOperation(self, name, args, cpu)
        self.issues += 1
        return None

    def advance(self, cpu):
        need(self.operation.finished and self.operation.captured.body is cpu._body,
             "Retirement used another physical return")

    def next_time(self):
        times = [x.due for x in self.endpoints.values() if x.due is not None]
        if self.operation is not None and self.operation.due is not None:
            times.append(self.operation.due)
        return min(times) if times else None

    def flow_to(self, at):
        bound = self.next_time()
        need(self.now <= at and (bound is None or at <= bound), "Crossed an actual due operation")
        for endpoint in self.endpoints.values():
            if endpoint.due is not None:
                endpoint.flow(at - endpoint.now)
        self.now = at

    def settle(self, *, raw_first=True):
        op = self.operation
        def priv():
            if op is not None and op.due == self.now:
                op.act()
        def material():
            for end in self.endpoints.values():
                if end.due == self.now:
                    end.act()
        for act in ((material, priv) if raw_first else (priv, material)):
            act()

    def run_to(self, at):
        while self.next_time() is not None and self.next_time() < at:
            self.flow_to(self.next_time())
            self.settle()
        self.flow_to(at)


class JoinedPorts(PrivatePorts):
    def __init__(self, native, owner, selector, endpoints, first_edge, periods):
        super().__init__(owner, selector, endpoints, first_edge, periods)
        self.native = native
        self.source = native.source

    def perform(self, name, args, cpu):
        if name in KINDS:
            return super().perform(name, args, cpu)
        need(name in paced.OrdinaryCycle.IO, "Missing physical port for this ordinary operation")
        return self.native.perform(name, args, cpu)

    def advance(self, cpu):
        info = cpu._io_info()
        if info is not None and info[0] in KINDS:
            super().advance(cpu)
        self.native.advance(cpu)


class PacingCycle(paced.OrdinaryCycle):
    IO = paced.OrdinaryCycle.IO | {"cpu_count"}

    def capture(self):
        state = super().capture()
        cpu = self.clock.cpu
        info = cpu._io_info()
        self.private = bool(state == "bound" and info and info[0] in KINDS)
        if self.private and not cpu.io_paid:
            need(cpu.complete(self.ports, pause_after_offer=True) == "waiting",
                 "Private parent returned at its first strobe")
        return state

    def offer(self):
        if not self.private:
            return super().offer()
        need(self.phase == "offer" and self.clock.now == self.time(1,2), "Wrong comparison phase")
        self.phase = "return"
        return "private-in-flight"

    def retire(self):
        if not self.private:
            return super().retire()
        need(self.phase == "return" and self.clock.now == self.time(1), "Wrong comparison return")
        self.phase = "closed"
        self.clock.active_cycle = None
        cpu = self.clock.cpu
        if self.captured is not cpu.pending:
            return "no-parent"
        # A failed initial local admission cannot silently be issued at return.
        if not cpu.io_paid:
            return "waiting"
        return "retired" if cpu.complete(self.ports) is True else "waiting"


class CommonClock:
    def __init__(self, native, ports):
        need(native.source is ports.source and native.cpu.bank.owner == ports.owner and
             native.now == ports.now == 0, "Mismatched physical CPU/source clocks")
        self.native, self.ports = native, ports

    def to(self, target):
        while True:
            next_private = self.ports.next_time()
            t = min(target,self.native.next_boundary(),
                    next_private if next_private is not None else target)
            self.native.advance_to(t)
            self.ports.flow_to(t)
            if t == target:
                return
            self.settle()

    def settle(self, *, native_first=True):
        def native():
            while self.native.due():
                self.native.edge(self.native.due()[0])
        def private():
            while self.ports.next_time() == self.ports.now:
                self.ports.settle()
        for act in ((native,private) if native_first else (private,native)):
            act()


def count_call(isa, compiled, selector, population, ecap):
    owner = (0,0)
    e = seat.charging.OperatingBank(owner, ecap, Q(ecap))
    U = raw.SourceWork(owner[0], 1<<60, 1<<60)
    source = paced.TimedSource(e, U)
    need(source.reform() == "formed-unpowered" and source.begin_entry(e)
         and source.entry_flow(Q(source.ENTRY_WORK, raw.CLEAR_RATE)), "No actual running local source")
    machine = ComparedParent(isa, compiled, bank=e)
    clock = paced.NativeClock(machine,source, external_receivers=True, adc_first=8*D, tx_first=13*D)
    units = {}
    key, threshold = 0,80
    hits = 0
    for slot in range(15):
        sel0,_ = selector.select(key,slot,0)
        origin,_,role = sel0
        need(origin != owner[0] and (origin,role) not in units, "Aliased compare supplier")
        # Legal bounded initial raw state, separately indexed by actual owner;
        # the arithmetic result below makes no assertion about sensor truth.
        origin_U = raw.SourceWork(origin,1<<60,0)
        rows = []
        worth = False
        for bank in (0,1):
            l = raw.RawLane(population,raw.LaneId(origin,bank,*owner),origin_U,
                            rows[0].captures if rows else None)
            cell = l.records[key]
            cell.value = 70 if slot%4 == bank else 92
            cell.set_ttl(5)
            worth |= cell.value <= threshold
            rows.append(l)
        hits += int(worth)
        units[origin,role] = RawRead(rows,role)
    native = paced.timed_ports(isa)(compiled,source)
    ports = JoinedPorts(native,owner,selector,units,D/4,[D/2,101*D/200]*5)
    common = CommonClock(clock,ports)
    machine.enter("count_fast",(key,threshold))
    # Sentinel is the existing ordinary harness return address in W[0].
    period = Q(100,101*2**26)
    count = 0
    while machine.pc != len(compiled.image) and count < 1000:
        cycle = PacingCycle(clock, ports, period)
        for edge,action in ((cycle.time(1,4),cycle.capture),(cycle.time(1,2),cycle.offer),
                            (cycle.time(1),cycle.retire)):
            common.to(edge)
            common.settle(native_first=count % 2 == 0)
            result = action()
        need(result == "retired", "A real compiled count step did not complete in its ordinary period")
        count += 1
    need(count == machine.retired == native.retire_notifications and ports.issues == 30
         and machine.result() == hits == 8 and machine.pc == len(compiled.image),
         "Different code count or private operation silently omitted")
    need(all(unit.cap.cell.spent == 2048 and unit.cap.payer.stock == 0
             and all(l.records[key].ttl == 5 for l in unit.lanes.values()) for unit in units.values()),
         "A bank read was cloned, received a new lease, or borrowed a remote impulse")
    for unit in units.values():
        unit.flow(clock.now - unit.now)
    clock.end_check()
    return dict(ordinary_retirements=count, comparisons=ports.issues, origins=len(units),
                true_source_banks_compared=2, count=hits, real_elapsed=clock.now,
                ordinary_period=period, receiver_E_sent_to_parents=e.supplied,
                raw_energy_per_backend=2048, source_clock_notifications=native.retire_notifications)

def support_bill():
    # The earlier selected current-compatible circuit has two actual power
    # conductors and nonzero control injection at both endpoints.
    original = electrical.bank_current_refinement_checks()
    base = electrical.private_point()
    tail = Q(base["private_suffix"])
    draw = Q(original["private_capsule_draw_upper"])
    reset = 256
    # In the worst placement all of reset is remote. It uses the same native
    # engine at a later time, so the peak work current is unchanged.
    driver_bound = draw + 900 * Q(reset + CONTROL - 928, 299)
    need(11 + 11*(11+2) + 11 <= CONTROL-928, "Timer bits, two tap gates or reset are unpaid")
    cap = seat.parent.PARENT
    need(driver_bound < DRIVER and GROUP + DRIVER + seat.parent.FRONT <= cap - 2048,
         "Insufficient actual root work or voltage reserve")
    elapsed = (11 * Q(101,200) + 2)*D + (GROUP + CONTROL + reset + seat.parent.FRONT) / RATE
    fast = Q(100,101*2**26)
    need(elapsed < 3*fast/4 and 2*D < fast/4 and elapsed < tail, "Comparison exceeds real CPU period")
    material = json.loads((HERE / "rx_restoration_results.json").read_text())["bill"]
    caprow = material["classes"]["capture"]
    cold = Q(caprow["low_start_all_slots_bound"])
    rearm = Q(caprow["rearm_after_full_working_pressure"])
    # An old fill can in turn trigger ONE old read after its completion.
    # Even an initial full fill remainder followed by the longer read/control
    # settlement is over before the sixth edge, including marker reformation.
    previous_tail = D + Q(101,100)*D
    form = max(previous_tail, cold) + rearm
    clearance = 5*D/2
    need(form < clearance, "Sixth-edge raw offer can collide with earlier activity")
    need(Q(13,1)/RATE < D/2, "One paid stage shift cannot settle by the next private edge")
    # Descriptor and result travels and actual raw-input wire settlement.
    # The raw grant completes before even the fastest eight-edge private read.
    raw_signal = Q(base["raw_control_settling_bound"])
    private_signal = Q(original["CPU_signal_settling_bound"])
    propagation = Q(base["private_round_trip_propagation"])
    cold_private = Q(original["nominal_cold_charge_bound"])
    need(2*D+raw_signal+Q(13,1)/RATE < 5*D/2 and cold_private+propagation/2+2*private_signal < D/2
         and propagation/2+2*private_signal < D/2 and Q(original["private_combined_reset"]) < D,
         "Actual private/raw signal and cold voltage windows do not fit")
    point = json.loads((HERE / "image_transport_results.json").read_text())["joined_point"]
    reaction = Q(point["reaction_slack"]) - Q(material["charged_extra_reaction"])
    need(reaction > 0 and Q(point["bath_margin"]) > 0, "Restored marker overlays exceed the previous point")
    return dict(ordinary_parent=cap, selected_group_work=GROUP, old_private_logic_work=9184,
                front=seat.parent.FRONT, functional_native_work=CONTROL, reset_work=reset,
                prior_remote_work=1344, worst_remote_if_all_reset_is_remote=1344+reset+CONTROL-928,
                earlier_electrical_bound=draw, driver_bound=driver_bound, reserved_driver=DRIVER,
                total_root_partition=GROUP+DRIVER+seat.parent.FRONT,
                root_reserve_beyond_partition=cap-GROUP-DRIVER-seat.parent.FRONT,
                suffix=elapsed, fastest_three_quarters=3*fast/4,
                raw_formation_and_old_tail=form, earliest_new_raw_offer=clearance,
                fresh_raw_and_wire_bound=2*D+raw_signal+Q(13,1)/RATE, raw_offer_to_sample_floor=clearance,
                first_private_sample=5*D, previous_eight_edge_may_miss_behind_old_fill=True,
                true_cold_private_voltage=cold_private, private_roundtrip=propagation,
                reset_with_nonzero_backfeed=original["private_combined_reset"],
                marker_and_seat_reaction_left=reaction)


def image_sites(isa, compiled):
    found = {name: [] for name in KINDS}
    for i in range(len(compiled.nodes)):
        op, dest, register, arity, prim = isa.decode(compiled.image[i])
        if op == isa.IO and prim < len(isa.PRIMITIVES) and isa.PRIMITIVES[prim] in KINDS:
            name = isa.PRIMITIVES[prim]
            need(arity == isa.PRIM_ARITY[name], "Malformed nominal compare")
            found[name].append((i, dest, register))
    return found


def trial(isa, compiled, sites, selector, population, cap, mode, name, slot, bank, key, bounds):
    owner = (0, 0)
    route, _ = selector.select(key & MASK, slot & MASK, bank & MASK)
    units = {}
    endpoint = None
    if route:
        origin, selected, role = route
        U = raw.SourceWork(origin, 2**60, 0)
        lanes = []
        for b in (0,1):
            lane = raw.RawLane(population, raw.LaneId(origin,b,*owner), U,
                               lanes[0].captures if lanes else None)
            lanes.append(lane)
            need(lane.records[key].role == role, "Installed word/role differs from the selected provider")
            lane.records[key].value = (73, 84)[b]
            lane.records[key].set_ttl(5)
        endpoint = RawRead(lanes, role, voltage=0 if mode == "unfunded" else 200)
        units[origin, role] = endpoint
        endpoint.cap.snapshot = 19
        if mode == "masked":
            lanes[bank].masked = True
        if mode in ("raw-stopped", "mutate-before", "mutate-after"):
            endpoint.cap.clock_enabled = False
        if mode == "partial":
            endpoint.cap.cell.stock = 511
        if mode == "old-sibling":
            endpoint.cap.cell.stock = 1024

    e = seat.charging.OperatingBank(owner, cap, Q(2**24))
    machine = ComparedParent(isa, compiled, bank=e)
    charge = seat.charging.JointCharge(e, machine, (), D)
    periods = [D/2, 101*D/200] * 5
    ports = PrivatePorts(owner, selector, units, 0 if bank == 0 else 101*D/200, periods)
    pc, dest, reg = sites[name][0]
    machine.pc = pc
    args = (slot, bank, key, *bounds)
    for i, v in enumerate(args):
        machine.R[reg+i] = v & MASK
    charge.flow_full_delivery(2*D, source_powered=False)
    need(machine.recharge() and machine.launch(), "Nominal CPU capture unavailable")
    before = machine.R[dest]
    need(machine.complete(ports) == "waiting" and machine.io_paid and ports.issues == 1,
         "One asynchronous admission did not retain the actual CPU")
    op = ports.operation
    need(machine.pending is op.captured and machine.retired == 0 and machine.R[dest] == before,
         "Return published at admission")
    machine.R[reg] = 14 if slot != 14 else 0
    # The physical return must use the captured register and body after this independent write.
    while op.stage != "arm":
        ports.flow_to(ports.next_time())
        ports.settle()
    ports.flow_to(op.due)
    if mode in ("old-fill", "old-sibling"):
        endpoint.flow(ports.now - endpoint.now)
    if mode == "old-sibling":
        endpoint.install_live_old(1-bank, key)
    if mode == "old-fill":
        need(endpoint.request(1-bank,key) == "offered" and endpoint.stage == "fill",
             "No earlier genuine sibling fill")
        need(endpoint.request(bank,key) == "busy", "Immediate eight-edge request replaced the sibling")
    ports.settle()
    while op.ticks < 6:
        ports.flow_to(ports.next_time())
        ports.settle()
    old_bit = None
    if mode == "old-fill":
        # The old sibling really committed first. With the immediate request
        # refused and no second strobe, this remains the eight-edge input.
        need(endpoint.cap.snapshot == (73,84)[1-bank] and op.raw_outcome == "offered",
             "Earlier result was skipped")
        old_bit = receiver.predicate(op.descriptor, endpoint.cap.snapshot)
        need(old_bit == 0, "No failed-window discriminator")
    if mode == "cut":
        machine.inhibit()
    if mode == "partial":
        ports.run_to(ports.now+D/2)
        need(endpoint.cap.cell.stock == 1023 and endpoint.tee.shunt_heat == 0,
             "Half fill created a free full capture")
    while op.ticks < 10:
        ports.flow_to(ports.next_time())
        ports.settle()
    ports.run_to(op.due)
    if mode == "mutate-before":
        endpoint.cap.snapshot = 101
    ports.settle()
    if mode == "mutate-after":
        endpoint.cap.snapshot = 101
    need(op.ticks == 11 and machine.complete(ports) == "waiting" and machine.retired == 0,
         "Strobe bypassed result propagation or private reset")
    while not op.finished:
        ports.flow_to(ports.next_time())
        ports.settle()
    outcome = machine.complete(ports)
    if mode == "cut":
        need(outcome == "waiting" and machine.retired == 0 and machine.R[dest] == before,
             "Paid old socket wrote across the real cutoff")
    else:
        need(outcome is True and machine.pc == pc+1 and machine.retired == 1
             and machine.R[dest] == op.bit and machine.child.return_consumed
             and not machine.fabric.token, "Return missed true routed CPU destination")
    if mode in ("old-sibling","old-fill"):
        need(op.raw_outcome == "offered" and endpoint.cap.snapshot == (73,84)[bank],
             "Old source-bank read preempted or rebound the requested read")
    expected = (MASK if route is None or mode == "masked" else
                101 if mode == "mutate-before" else
                19 if mode in ("raw-stopped","unfunded","mutate-after") else (73,84)[bank])
    need(op.value == expected and op.bit == receiver.predicate(op.descriptor, expected),
         "Comparison consumed the wrong timed operand")
    if endpoint:
        endpoint.flow(ports.now - endpoint.now)
        need(U.stock == 0, "Raw fill borrowed a remote impulse")
        if mode == "partial":
            need(endpoint.tee.received == 1024 and endpoint.tee.shunt_heat == 511,
                 "Partly charged old capture was lost or used twice")
    charge.balance()
    return dict(case=mode, op=name, pc=pc, socket_register=dest, selection=route,
                captured_args=args, raw=op.value, bit=op.bit, timer_edges=op.ticks,
                raw_request=op.raw_outcome, early_issue_counterfactual_bit=old_bit, raw_shunt=endpoint.tee.shunt_heat if endpoint else 0,
                physical_retirements=machine.retired, E_draw=e.supplied, elapsed=ports.now,
                private_issue_count=ports.issues)


def generate():
    isa = seat.program.load_isa()
    compiled, _ = seat.candidate(isa)
    signature = seat.program.hash_text(json.dumps(compiled.image))
    previous = json.loads((HERE/"image_transport_results.json").read_text())
    need(signature == previous["new_image"], "Changed binary")
    population = json.loads((HERE/"threshold_initialization_results.json").read_text())["population"]
    selector = seat.legacy.GroupSelector(population, 0)
    sites = image_sites(isa, compiled)
    cases = [
        ("qualified", "fast_cmp", 0, 0, 0, (73,)),
        ("qualified", "fast_range", 14, 1, 2002, (83,85)),
        ("partial", "fast_equal", 1, 1, 1, (84,)),
        ("masked", "fast_cmp", 3, 1, 0, (500,)),
        ("raw-stopped", "fast_equal", 1, 0, 3, (19,)),
        ("unfunded", "fast_cmp", 4, 1, 1, (18,)),
        ("old-sibling", "fast_equal", 0, 0, 1, (73,)),
        ("old-fill", "fast_equal", 0, 1, 1, (84,)),
        ("cut", "fast_equal", 3, 1, 0, (84,)),
        ("mutate-before", "fast_cmp", 10, 0, 0, (20,)),
        ("mutate-after", "fast_cmp", 10, 0, 0, (20,)),
        ("missing-key", "fast_equal", 0, 1, 2, (-1,)),
        ("invalid-slot", "fast_range", -1, 1, 0, (-2,100)),
    ]
    with localcontext() as context:
        context.prec = 75
        cap = int(Q(seat.parent.cost_bounds()["actual_bank_capacity"]))
        rows = [trial(isa,compiled,sites,selector,population,cap,*case) for case in cases]
        count = count_call(isa,compiled,selector,population,cap)
    before, after = (next(r for r in rows if r["case"] == kind) for kind in ("mutate-before","mutate-after"))
    need(before["bit"] == 0 and after["bit"] == 1 and before["elapsed"] == after["elapsed"],
         "Same-time raw effect lost its causal order")
    return seat.incumbent.normalize(dict(
        source_image=signature, sites={k:[x[0] for x in v] for k,v in sites.items()},
        price=support_bill(), cases=rows, compiled_count_fast=count, source_manifests={n:seat.program.digest(HERE/n) for n in (
            "PRIVATE-COMPARISON.md","private_comparison.py","parent_retirement.py","shared_bank_charging.py","rx_restoration.py",
            "rx_restoration_results.json","return_seat.py","image_transport_results.json",
            "legacy_realization.py","input_lifecycle.py","../local-control/receiver_model.py",
            "../local-control/receiver_power_model.py","../local-control/receiver_power_results.json")},
        all_modes_integrated=False, every_instruction_and_earlier_prefix_serviced=False))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    opts = parser.parse_args()
    path = HERE / "private_comparison_results.json"
    result = json.dumps(generate(), sort_keys=True, indent=2) + "\n"
    if opts.write:
        path.write_text(result, encoding="utf-8", newline="\n")
    else:
        need(result == path.read_text(encoding="utf-8"), "Private comparison receipt differs")
    print("Verified timed private return, raw/cut ordering and shared-cell affordability")
