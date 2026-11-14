"""Finite candidate field/word port source and exact local accounting.

The executable contains source transition fragments, not a complete hybrid
dispatcher or the RP0-RP6 controller proof. See THRESHOLD-FIELD-SOURCE.md.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass, field
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = "eb89da81a0fdc7ccd56323ed4b18d75fffd88752"
PREFIX = "theories-and-designs/byzantine-control/"
L = 8192 * 192
DEGREE = 40
U_BIT = F(1, 1000 * L)
FORCE = F(101, 100) * U_BIT
THETA = 13 * U_BIT
Z_MAX = F(1621, 20) * U_BIT
BIT_SPEED = F(2**32)
NATIVE_GAIN = F(2**64)
NATIVE_FORCE = THETA + Z_MAX + BIT_SPEED / NATIVE_GAIN
REACTION = F(81, 250)  # Field reaction .3232 plus both native word actuators.
SET_ENERGY = F(2**20)
SET_CLOCK = F(2**20)
SET_REFILL = F(1, 128)
WORD_CLOCK = F(2**30)
WORD_ENERGY = F(20480)
WORD_MASK = (1 << 256) - 1
PULSE_EDGES = 2**21
PULSE_COUNTER_BITS = 22
PULSE_COUNTER_CAP = 2**PULSE_COUNTER_BITS-1
PULSE_ENERGY = F(2**26)
TRIGGER_ENERGY = F(4096)
RESET_ENERGY = F(2**14)
RESET_SOURCE_ENERGY = F(4096)
RESET_RECEIVER_ENERGY = RESET_ENERGY-RESET_SOURCE_ENERGY
SETTER_RESET_ENERGY = F(2**16)
RESET_REFILL = F(100000)
DUMP_FLOOR = F(1,2)
DUMP_TIME = F(100)
RESET_CLEAR_TIME = F(1,64)
RESET_ABORT_TIME = F(1,64)
CONTROL_TAIL = F(64,2**20)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def exact(value, label="value"):
    need(type(value) in (int, F), label + " must be exact int/Fraction")
    return F(value)


def natural(value, label="count"):
    need(type(value) is int and value >= 0, label + " must be a natural integer")
    return value


def clip(value, low, high):
    return max(low, min(high, value))


def digest(text):
    return sha256(text.replace("\r\n", "\n").encode()).hexdigest()


def frozen(name):
    return subprocess.check_output(["git", "show", BASE + ":" + PREFIX + name],
                                   cwd=REPO).decode("utf-8-sig").replace("\r\n", "\n")


INPUTS = (
    "local-control/PORT-SOURCE.md", "local-control/PORT-RESOURCES.md",
    "local-control/port_source_results.json", "local-control/port_resource_results.json",
    "local-control/resource_results.json", "portability/PULSE-FIELDS.md",
    "portability/pulse_model.py", "portability/pulse_results.json",
    "portability/publication_timing.py", "portability/publication_timing_results.json",
    "portability/THRESHOLD-PUBLICATION.md", "portability/threshold_program_source.py",
    "portability/threshold_program_model.py", "portability/threshold_program_results.json",
)


def inputs():
    texts = {name: frozen(name) for name in INPUTS}
    for name in ("pulse_results.json", "publication_timing_results.json", "threshold_program_results.json"):
        record = json.loads(texts["portability/" + name])
        for source, expected in record.get("sources_sha256_lf", {}).items():
            need(digest(frozen("portability/" + source)) == expected,
                 "Frozen transitive binding differs: " + source)
    return texts, {name: digest(text) for name, text in texts.items()}


@dataclass
class WorkCell:
    """One actual stock; reservations/owners cannot create another energy copy."""
    capacity: F
    stock: F
    input_cap: F = F(0)
    delivered_input: F = F(0)
    upstream_input: F = F(0)
    spent: F = F(0)
    dumped: F = F(0)
    busy: bool = False

    def __post_init__(self):
        self.capacity=exact(self.capacity);self.stock=exact(self.stock)
        self.input_cap=exact(self.input_cap)
        need(0<=self.stock<=self.capacity and self.input_cap>=0,"Invalid physical work cell")

    def debit(self,work):
        work=exact(work)
        need(work>=0,"Negative physical work debit")
        if self.stock<work:return False
        self.stock-=work;self.spent+=work
        return True

    def charge(self,dt,efficiency=F(1,2),connected=True):
        dt=exact(dt);efficiency=exact(efficiency)
        need(dt>=0 and F(1,2)<=efficiency<=1,"Invalid physical charge interval")
        if not connected:return F(0)
        delivered=min(self.capacity-self.stock,efficiency*self.input_cap*dt)
        self.stock+=delivered;self.delivered_input+=delivered
        self.upstream_input+=delivered/efficiency
        return delivered

    def dump(self,dt):
        # Constant rated dissipation until a positive low-work floor. This is
        # an actual work port, not assignment of zero or exponential erasure.
        dt=exact(dt);need(dt>=0,"Negative dump interval")
        loss=min(max(F(0),self.stock-DUMP_FLOOR),self.capacity/DUMP_TIME*dt)
        self.stock-=loss;self.dumped+=loss
        return loss


@dataclass(frozen=True)
class Destination:
    body: str
    bank: int
    bit: int


@dataclass
class SettingWriter:
    """One finite hardwired setter; no host-language controller executes here.

    Each generator yield is a bounded bit comparator/capture, mux hop, latch,
    or scrub microstep. Its one operation returns only after actual refill.
    Destination presentation is decoded from the physical tree path, not read
    from a mutable runtime routing table. Circuit refinement remains explicit.
    """
    targets: tuple[str, ...]
    phase: str = "ready"
    energy: F = SET_ENERGY
    cut: bool = False
    held: dict = field(default_factory=dict)
    steps: int = 0
    logical_cost: F = F(0)
    returned: bool | None = None
    latched: tuple | None = None
    generator: object = None
    parent_record: tuple|None = None
    parent_live: bool = False
    native_inhibit: bool = False
    reset_stock: F = F(0)
    reset_reserve: WorkCell = field(init=False)

    def __post_init__(self):
        need(type(self.targets) is tuple and len(self.targets)==DEGREE
             and all(type(t) is str and t for t in self.targets)
             and len(set(self.targets))==DEGREE,
             "Setter requires exactly40 distinct fixed physical targets")
        self.energy=exact(self.energy,"Setter stock")
        need(0<=self.energy<=SET_ENERGY,"Setter stock outside physical capacity")
        self.reset_reserve=WorkCell(SETTER_RESET_ENERGY,exact(self.reset_stock),
                                   2*SETTER_RESET_ENERGY/RESET_REFILL)

    def __setattr__(self,name,value):
        if name=="targets" and hasattr(self,"targets"):
            need(value==self.targets,"Fixed setter destinations cannot be rebound")
        object.__setattr__(self,name,value)

    def issue(self, args):
        if self.cut or self.native_inhibit:
            return "cut"
        if self.phase != "ready":
            return "busy"
        if self.energy < SET_ENERGY:
            return "unfunded"
        if type(args) is not tuple or len(args) != 4 or any(type(v) is not int or not -(1 << 255) <= v < (1 << 255) for v in args):
            return "malformed"
        # Alias the actual parent's already captured immutable operands. The
        # child's1024-bit copy is made by the counted capture microsteps.
        self.parent_record=args;self.parent_live=True
        self.latched = self.parent_record
        self.phase = "pending"
        self.returned = None
        self.steps = 0
        self.logical_cost = F(0)
        self.generator = self.microprogram()
        return "latched"

    def microprogram(self):
        # Four actual 256-bit latches; no untouched private state is consumed.
        bits = [[0] * 256 for _ in range(4)]
        for a in range(4):
            for j in range(256):
                bits[a][j] = (self.latched[a] >> j) & 1
                yield "capture"
        tests = ((0, len(self.targets), "lt"), (1, 2, "lt"), (2, L, "lt"),
                 (3, 0, "eq"), (3, 1, "eq"), (3, WORD_MASK, "eq"))
        answers = []
        for a, bound, relation in tests:
            order = 0
            for j in range(255, -1, -1):
                other = (bound >> j) & 1
                if order == 0 and bits[a][j] != other:
                    order = -1 if bits[a][j] < other else 1
                yield "compare-bit"
            answers.append(order < 0 if relation == "lt" else order == 0)
        valid = all(answers[:3]) and any(answers[3:])
        if valid:
            # Hierarchy: six target bits, one bank bit, twenty-one bit bits.
            path = []
            for a, width in ((0, 6), (1, 1), (2, 21)):
                for j in range(width - 1, -1, -1):
                    path.append(bits[a][j])
                    yield "physical-mux-hop"
            target = sum(path[j] << (5-j) for j in range(6))
            bank = path[6]
            bit = sum(path[7+j] << (20-j) for j in range(21))
            key = Destination(self.targets[target], bank, bit)
            value = -1 if answers[5] else 1 if answers[4] else 0
            # Two staging bits plus one active-latch selector; samplers cannot
            # observe a torn two-bit ternary code while staging is written.
            yield "stage-bit-0"
            yield "stage-bit-1"
            self.held[key] = value
            yield "commit-selector"
        for a in range(4):
            for j in range(256):
                bits[a][j] = 0
                yield "scrub"
        self.returned = valid
        self.phase = "recharging"
        self.latched = None

    def step(self):
        if self.native_inhibit:return "inhibited-wait"
        if self.phase != "pending":
            return "wait"
        if not self.parent_live:return "retired-wait"
        if self.energy <= 1 + 16:
            # A physical clock-gated hold, not an exception or a new rejection
            # event. The latched operands and partially executed microprogram
            # remain; no positive work or late fresh capture occurs here.
            return "unfunded-wait"
        try:
            event = next(self.generator)
        except StopIteration:
            return "recharging"
        self.energy -= 16
        self.logical_cost += 16
        self.steps += 1
        return event

    def recharge(self, dt, efficiency=F(1, 2), connected=True):
        dt = exact(dt)
        efficiency = exact(efficiency)
        need(dt >= 0 and F(1, 2) <= efficiency <= 1, "Invalid charger interval")
        if self.phase != "recharging" or not connected:
            return "wait"
        # Actual installed input cap; not inferred from a refill deadline.
        self.energy = min(SET_ENERGY, self.energy + efficiency * (2*SET_ENERGY/SET_REFILL)*dt)
        if self.energy == SET_ENERGY:
            self.phase = "ready"
            self.parent_live=False;self.parent_record=None
            return "done"
        return "partial"


def bit_flow(x, external, native, dt, open_contact=True, native_engaged=False):
    """Exact constant-input segment of the retained physical bit coordinate."""
    x, external, native, dt = map(exact, (x, external, native, dt))
    need(-1 <= x <= 1 and dt >= 0, "Invalid retained bit segment")
    need(abs(external) <= Z_MAX and abs(native) <= NATIVE_FORCE, "Unrated bit input")
    z = (external if open_contact else F(0)) + native
    mobility = NATIVE_GAIN if native_engaged else F(1)
    velocity = mobility * (max(z-THETA, 0) if z >= 0 else -max(-z-THETA, 0))
    velocity = clip(velocity, -BIT_SPEED, BIT_SPEED)
    after = clip(x + dt*velocity, F(-1), F(1))
    need(z * (after-x) >= 0, "Bit constitutive law generated work")
    return after


def native_word(initial, word, opposing=True, address=0, *, parent=None):
    """Literal 192-bit retained native overwrite fragment with paid steps.

    The parent latches its local physical body/address. It blocks later fetches
    until completion; cutoff cannot cancel its already paid bit suffix.
    This function does not prove a whole-system atomic-ISA refinement.
    """
    need(len(initial) == 192 and type(word) is int and 0 <= word <= WORD_MASK,
         "Invalid native word operand wire")
    need(type(address) is int and 0<=address<=WORD_MASK,
         "Native address must be an actual unsigned256-bit wire value")
    need(isinstance(parent,WorkCell) and parent.capacity==WORD_ENERGY,
         "Native word requires its actual finite parent work cell")
    cells = list(map(exact, initial))
    need(all(-1 <= x <= 1 for x in cells), "Invalid native bit initial state")
    if parent.busy or parent.stock<2080*8+2:return cells,0,F(0),False
    parent.busy=True
    steps=0;address_bits=[]
    for j in range(256):
        address_bits.append((address>>j)&1)
        steps+=1
        need(parent.debit(8),"Native address capture lost its funded parent")
    order=0
    for j in range(255,-1,-1):
        limit=(8192>>j)&1
        if order==0 and address_bits[j]!=limit:
            order=-1 if address_bits[j]<limit else 1
        steps+=1
        need(parent.debit(8),"Native address comparison lost its funded parent")
    if order>=0:
        parent.busy=False
        return cells,steps,F(0),False
    physical_work = F(0)
    latched = []
    for bit in range(192):
        latched.append((word >> bit) & 1)
        steps += 1
        need(parent.debit(8),"Native operand capture lost its funded parent")
    min_tick = F(100, 101) / WORD_CLOCK
    for bit, value in enumerate(latched):
        sign = 2*value-1
        drive = sign*NATIVE_FORCE
        external = -sign*Z_MAX if opposing else sign*Z_MAX
        steps += 1  # Energize the finite native-mobility/write mode.
        need(parent.debit(8),"Native drive launch lost its funded parent")
        start = cells[bit]
        for tick in range(4):
            # Arbitrary first clock phase may deliver the first edge at once.
            cells[bit] = bit_flow(cells[bit], external, drive,
                                  F(0) if tick == 0 else min_tick,
                                  native_engaged=True)
            steps += 1
            need(parent.debit(8),"Native clock lost its funded parent")
        physical_work += abs(drive*(cells[bit]-start))
        steps += 1  # Remove the native write force/mobility request.
        need(parent.debit(8),"Native release lost its funded parent")
        need(cells[bit] == sign, "Funded bit pulse did not reach its actual endpoint")
    for bit in range(192):
        latched[bit] = 0
        steps += 1
        need(parent.debit(8),"Native scrub lost its funded parent")
    steps += 32  # Bounded parent completion/control latch transitions.
    need(parent.debit(32*8+1),"Native completion/mechanical allowance lost its parent")
    need(steps == 2080, "Native microstep count changed")
    parent.busy=False
    return cells, steps, physical_work,True


def converter_pair(force, bit_speed, reaction_column, recipient_velocities):
    """Port identity: recipient velocities are D*i plus pose velocities."""
    force, bit_speed = exact(force), exact(bit_speed)
    a = tuple(map(exact, reaction_column));v = tuple(map(exact, recipient_velocities))
    need(len(a) == len(v) and sum(map(abs, a)) <= 1, "Reaction column exceeds joint capacity")
    need(abs(force) <= FORCE and abs(bit_speed) <= BIT_SPEED, "Converter hard range violated")
    reaction = tuple(ai*force for ai in a)
    motor = force*(bit_speed-sum(ai*vi for ai, vi in zip(a, v)))
    bit = force*bit_speed
    recipients = -sum(ri*vi for ri, vi in zip(reaction, v))
    need(motor == bit+recipients, "Virtual-work pairing failed")
    return motor, reaction


def counter_tick(value, width):
    """One literal saturating down-counter tick; pad its native pipeline to64."""
    natural(value);natural(width)
    need(0 < width <= 22 and value < 2**width, "Counter outside installed width")
    bits=[(value>>i)&1 for i in range(width)]
    if value==0:return 0, F(4), 64
    borrow=1;changed=0
    for i in range(width):
        if borrow:
            old=bits[i]
            bits[i]=old^1
            borrow=1-old
            changed+=1
    result=sum(bit<<i for i,bit in enumerate(bits))
    need(result==value-1, "Native counter changed the wrong count")
    return result,F(changed,2)+4,64


@dataclass
class PulseSelector:
    """One motor, three slots: native occupancy does not multiply output."""
    slots: list = field(default_factory=lambda: [None, None, None])
    pending: list = field(default_factory=lambda: [None, None, None])
    force: F = F(0)
    cut: bool = False
    native_inhibit: bool = False
    ep_charging: bool = True
    initial_energy: tuple = (PULSE_ENERGY,)*3
    initial_trigger_energy: tuple = (TRIGGER_ENERGY,)*3
    initial_reset_energy: tuple = (F(0),F(0))
    energy: list = field(init=False)
    trigger_energy: list = field(init=False)
    reset_reserve: WorkCell = field(init=False)
    reset_source_reserve: WorkCell = field(init=False)
    withdrawal_owner: int|None = None
    reset_motor_owner: bool = False
    reset_actuator_failed: bool = False
    motor_input: F = F(0)
    motor_output: F = F(0)
    motor_heat: F = F(0)

    @property
    def edge_count(self):
        return PULSE_EDGES

    @staticmethod
    def valid_slot(slot):
        return type(slot) is int and 0<=slot<3

    def __post_init__(self):
        need(type(self.slots) is list and len(self.slots)==3
             and type(self.pending) is list and len(self.pending)==3,
             "Selector has exactly three installed slots")
        for state in self.slots:
            need(state is None or (type(state) is list and len(state)==2
                 and type(state[0]) is int and state[0] in (-1,0,1)
                 and type(state[1]) is int and 0<=state[1]<=PULSE_COUNTER_CAP),
                 "Pulse state exceeds its ternary/counter wires")
        need(all(packet is None for packet in self.pending),
             "Initial trigger debt needs its actual capture/entry map")
        # Initial values populate three distinct installed registers. Python
        # container aliases cannot turn two physical counters into one store.
        self.slots=[None if state is None else list(state) for state in self.slots]
        self.pending=list(self.pending)
        self.force=exact(self.force,"Initial field force")
        need(abs(self.force)<=FORCE,"Initial field exceeds installed amplitude")
        need(type(self.initial_energy) is tuple and len(self.initial_energy)==3
             and type(self.initial_trigger_energy) is tuple and len(self.initial_trigger_energy)==3,
             "Initial work values must name three distinct installed cells")
        self.energy=[WorkCell(PULSE_ENERGY,exact(x),2*PULSE_ENERGY/RESET_REFILL)
                     for x in self.initial_energy]
        self.trigger_energy=[WorkCell(TRIGGER_ENERGY,exact(x),2*TRIGGER_ENERGY/RESET_REFILL)
                             for x in self.initial_trigger_energy]
        need(type(self.initial_reset_energy) is tuple and len(self.initial_reset_energy)==2,
             "Reset work names separate source and receiver stores")
        self.reset_source_reserve=WorkCell(RESET_SOURCE_ENERGY,exact(self.initial_reset_energy[0]),
                                          2*RESET_SOURCE_ENERGY/RESET_REFILL)
        self.reset_reserve=WorkCell(RESET_RECEIVER_ENERGY,exact(self.initial_reset_energy[1]),
                                   2*RESET_RECEIVER_ENERGY/RESET_REFILL)

    def counter_bound_holds(self):
        """Counter-only proof query; supplies neither funding nor formation."""
        return all(s is None or 0<s[1]<=self.edge_count for s in self.slots)

    def fault_counter(self,slot,value):
        # Explicit physical-register mutation, outside ordinary payload access.
        # It does not silently restore nominal expiry or energy qualification.
        if not self.valid_slot(slot) or type(value) is not int or not 0<=value<=PULSE_COUNTER_CAP:
            return "reject"
        if self.slots[slot] is None:return "inactive"
        self.slots[slot][1]=value
        return "faulted"

    def capture(self, slot, value, *, now=F(0)):
        now=exact(now)
        if not self.valid_slot(slot) or type(value) is not int or value not in (-1,0,1):
            return "reject"
        if self.cut:
            return "cut"
        if self.pending[slot] is not None:
            return "pending-busy"
        if self.trigger_energy[slot].stock<TRIGGER_ENERGY:return "unfunded"
        self.trigger_energy[slot].busy=True
        # born/deadline are analyst annotations for the bounded propagation
        # state; they are not stored absolute runtime timestamps.
        self.pending[slot]=(value,now,now+1)
        return "latched"

    def deliver(self, slot, *, now=F(0)):
        now=exact(now)
        if not self.valid_slot(slot):return "reject"
        packet=self.pending[slot]
        if packet is None:return "absent"
        value,born,deadline=packet
        if now<born:return "not-arrived"
        if self.trigger_energy[slot].stock<TRIGGER_ENERGY:return "unfunded-pending"
        self.pending[slot]=None
        need(self.trigger_energy[slot].debit(TRIGGER_ENERGY),"Pending trigger was spent twice")
        self.trigger_energy[slot].busy=False
        if now>deadline:return "expired"
        if self.native_inhibit:return "inhibited"
        if self.slots[slot] is not None:
            return "busy"
        if self.withdrawal_owner==slot:return "withdrawing"
        if self.energy[slot].stock<PULSE_ENERGY:return "unfunded"
        need(self.energy[slot].debit(128),"Accepted pulse lacks its setup work")
        self.slots[slot] = [value,self.edge_count]
        return "active"

    def trigger(self, slot, value, *, now=F(0)):
        status=self.capture(slot,value,now=now)
        return self.deliver(slot,now=now) if status=="latched" else status

    def abort_pending(self,slot):
        if not self.valid_slot(slot):return "reject"
        if not self.cut or not self.native_inhibit:return "inhibit-required"
        if self.pending[slot] is None:return "absent"
        if self.reset_source_reserve.stock<33 or self.reset_reserve.stock<33:
            return "reset-unfunded-wait"
        self.reset_source_reserve.debit(32);self.reset_reserve.debit(32)
        # Source and receiver control-valid claims are consumed only after
        # their write gates close and the already emitted physical tail settles.
        # Unspent trigger work stays in this same cell; no energy is erased.
        self.pending[slot]=None;self.trigger_energy[slot].busy=False
        return "aborted"

    def clock_edge(self, slot):
        if not self.valid_slot(slot):return "reject"
        if self.native_inhibit:return "inhibited-wait"
        if self.slots[slot] is None:return "idle"
        # Padding each bounded counter operation to15 work is within its16
        # primitive allowance. Expiry also owns its fixed selector work.
        work=F(47) if self.slots[slot][1]<=1 else F(15)
        if self.energy[slot].stock<work+1:return "unfunded-wait"
        self.energy[slot].debit(work)
        if self.slots[slot][1]>0:self.slots[slot][1]-=1
        if self.slots[slot][1]==0:
            self.slots[slot]=None
            if not any(s is not None for s in self.slots) and self.force!=0:
                self.withdrawal_owner=slot
            return "expired"
        return "active"

    def selected(self):
        return next((s[0] for s in self.slots if s is not None), 0)

    def refill(self,dt):
        dt=exact(dt)
        for i,cell in enumerate(self.energy):
            if self.slots[i] is None and self.withdrawal_owner!=i:
                cell.charge(dt,connected=self.ep_charging)
        for i,cell in enumerate(self.trigger_energy):
            if self.pending[i] is None:cell.charge(dt)

    def flow(self, dt, mode="nominal", relative_velocity=F(0)):
        dt=exact(dt);relative_velocity=exact(relative_velocity)
        maximum=BIT_SPEED+22*(F(2**20)+22*(2**16+REACTION))/16+F(11,10)
        need(dt>=0 and abs(relative_velocity)<=maximum,"Invalid field flow/velocity")
        active=next((i for i,s in enumerate(self.slots) if s is not None),None)
        owner=active if active is not None else self.withdrawal_owner
        command=0 if self.reset_motor_owner else self.selected()
        cell=self.reset_reserve if self.reset_motor_owner else self.energy[owner] if owner is not None else None
        if self.reset_motor_owner:
            # Old pulse-control modes have lost this path. A physically failed
            # reset actuator remains a distinct admitted failure outcome.
            mode="jam" if self.reset_actuator_failed else "nominal"
        target = U_BIT*command
        if mode == "wrong":target = -target
        elif mode == "jam":target = self.force
        else:need(mode == "nominal", "Unknown field mode")
        slew = FORCE/F(1000) if command == 0 else 2*FORCE/F(1000)
        needed=dt
        if command==0 and mode!="jam":needed=min(dt,abs(self.force)/slew)
        if needed==0:return self.force
        if cell is None:
            # No energized driver job: retained field controls are not a work
            # source. This is the stated raw power-disconnect outcome.
            self.force=F(0)
            return self.force
        funded=min(needed,max(F(0),(cell.stock-1)/8))
        old=self.force
        change=clip(target-old,-slew*funded,slew*funded)
        after=clip(old+change,-FORCE,FORCE)
        moving=min(funded,abs(target-old)/slew)
        integral=(old+after)*moving/2+after*(funded-moving)
        output=relative_velocity*integral;work=8*funded
        need(output<=work and cell.debit(work),"Motor job exceeded its actual escrow")
        self.motor_input+=work;self.motor_output+=output;self.motor_heat+=work-output
        self.force=after
        if funded<needed:
            # One physical low-stock disconnect spends the residual floor.
            # The source law permits this faster lost-output branch; nominal
            # expiry and reformation use separately paid withdrawal instead.
            relay=min(F(1),cell.stock);cell.debit(relay)
            self.motor_input+=relay;self.motor_heat+=relay
            self.force=F(0)
        if self.force==0 and active is None:self.withdrawal_owner=None
        return self.force


@dataclass
class DiagnosticPulseSelector(PulseSelector):
    """Short-count test fixture; never a hardware lifetime/initial-entry input."""
    fixture_edges: int = 2

    def __post_init__(self):
        super().__post_init__()
        need(type(self.fixture_edges) is int and 0<self.fixture_edges<=PULSE_COUNTER_CAP,
             "Diagnostic counter count outside native width")

    @property
    def edge_count(self):
        return self.fixture_edges


def reformation_bounds():
    parent=F(1,64);delivery=F(1)
    tail=parent+delivery+CONTROL_TAIL
    # These durations are analyst bounds on actual locally held modes and
    # finite native jobs, not global runtime timestamps.
    commutation=delivery+RESET_CLEAR_TIME
    total=tail+RESET_REFILL+commutation+DUMP_TIME+1000+RESET_CLEAR_TIME+RESET_ABORT_TIME+RESET_REFILL
    old=parent+F(2198154)
    need(DUMP_TIME>tail,"Old physical parents/native writes can outlast the inhibited drain")
    need(total<old,"Reformation exceeds the existing preparation allowance")
    return dict(old_parent_and_native_tail=tail,reset_reserve_refill=RESET_REFILL,
                mode_commutation=commutation,dump=DUMP_TIME,withdrawal=F(1000),
                native_clear=RESET_CLEAR_TIME,parent_abort=RESET_ABORT_TIME,
                final_refill=RESET_REFILL,prepared_bound=total,
                old_preparation_allowance=old,strict_slack=old-total)


def finite_flight_checks():
    """Finite relative-state counterpart of the analyst deadline annotations."""
    rows=[]
    for raw in range(4):
        bits=[raw&1,(raw>>1)&1]
        stages=[None]*6;writes=0
        for stage in range(6):
            stages[stage]=[bits[0],bits[1],1]
            writes+=3
            bits=stages[stage][:2]
        received=bits[0]+2*bits[1]
        need(received==raw,"Fixed lane changed the captured physical payload")
        remaining=8;timer_work=F(0)
        for _ in range(8):
            remaining,work,_=counter_tick(remaining,4);timer_work+=work
        work=2*writes+timer_work+64*16
        need(remaining==0 and work<=TRIGGER_ENERGY,"Finite propagation/timer profile exceeds its store")
        rows.append(dict(raw=raw,delivered=received,bit_writes=writes,work=work))
    need(F(6,8)<1 and F(8,8)==1,"Relative lane timing differs")
    return dict(native_stages=6,relative_counter_bits=4,timeout_edges=8,
                local_clock_min=8,local_clock_max=F(202,25),
                delivery_max=F(3,4),disposal_max=1,rows=rows,
                scope="conforming fixed-lane operations under declared native prices/rate; no global timestamp storage")


class PulseReformation:
    """Executed local reset episode over actual retained component objects.

    Its phase list records a fixed physical input sequence. Implementing those
    held modes in the ordinary programme/cam remains an integration obligation.
    The sequence never reads P, a healthy-donor label, or a semantic READY bit.
    """
    def __init__(self,selector,setter=None):
        need(isinstance(selector,PulseSelector) and type(selector) is PulseSelector,
             "Reformation requires the actual hardware counter class")
        need(setter is None or isinstance(setter,SettingWriter),"Untyped setter endpoint")
        self.selector=selector;self.setter=setter;self.phase="idle"
        self.elapsed=F(0);self.events=[]
        self.native_bits=[1]*1024
        self.setter_bits=[1]*4096 if setter is not None else []
        # Bit decomposition of the same installed slot registers. Inactive
        # register residue may be arbitrary; all1024 reset addresses are swept.
        for slot,state in enumerate(selector.slots):
            base=25*slot
            self.native_bits[base]=int(state is not None)
            if state is not None:
                value,count=state;encoded={0:0,1:1,-1:2}[value]
                for j in range(2):self.native_bits[base+1+j]=(encoded>>j)&1
                for j in range(22):self.native_bits[base+3+j]=(count>>j)&1

    def clear_native_bit(self,index):
        self.native_bits[index]=0
        if index<75:
            slot=index//25;base=25*slot
            active=self.native_bits[base]
            value=sum(self.native_bits[base+1+j]<<j for j in range(2))
            count=sum(self.native_bits[base+3+j]<<j for j in range(22))
            self.selector.slots[slot]=[{0:0,1:1,2:-1,3:0}[value],count] if active else None

    def mark(self,phase,dt=F(0)):
        self.phase=phase;self.elapsed+=dt;self.events.append((phase,self.elapsed))

    def run(self,*,charger_bypass=False,reset_chargers_connected=True):
        if self.phase!="idle":return "busy"
        p=self.selector;s=self.setter;b=reformation_bounds()
        # Start at an actual source cut. No mutable native control flag is
        # assumed cleared here; pending parents remain actual one-shot records.
        p.cut=True
        if s is not None:s.cut=True
        self.mark("cut")
        # Pending control continuations are not assumed to complete from their
        # nominal timestamp or depleted Em. Physical in-flight effects settle
        # under the separate tail law; the remaining claims are aborted below.
        p.flow(b['old_parent_and_native_tail'],mode="jam")
        self.mark("initial-physical-tail-window",b['old_parent_and_native_tail'])
        p.flow(RESET_REFILL,mode="jam")
        # Old controller states may keep every ordinary charger connected.
        # Their actual positive input is accounted, never used as a drain aid.
        for cell in p.energy:cell.charge(RESET_REFILL)
        p.reset_reserve.charge(RESET_REFILL,connected=reset_chargers_connected)
        p.reset_source_reserve.charge(RESET_REFILL,connected=reset_chargers_connected)
        if s is not None:s.reset_reserve.charge(RESET_REFILL,connected=reset_chargers_connected)
        self.mark("reset-reserves-charged",RESET_REFILL)
        if p.reset_reserve.stock<RESET_RECEIVER_ENERGY or p.reset_source_reserve.stock<RESET_SOURCE_ENERGY or s is not None and s.reset_reserve.stock<SETTER_RESET_ENERGY:
            return "reset-unfunded-wait"
        # Added physical poles: divert Ep and setter recharge to local dump,
        # block old native writes, and give the sole motor to the reset reserve.
        need(p.reset_reserve.debit(128) and p.reset_source_reserve.debit(128),
             "Reset endpoint commutations were not separately funded")
        p.flow(b['mode_commutation'],mode="jam")
        for cell in p.energy:cell.charge(b['mode_commutation'])
        p.ep_charging=charger_bypass;p.native_inhibit=True;p.reset_motor_owner=True
        if s is not None:
            need(s.reset_reserve.debit(128),"Setter isolation was not funded")
            s.native_inhibit=True
        self.mark("isolated",b['mode_commutation'])
        p.flow(DUMP_TIME)  # Same single motor now draws only its reset reserve.
        for cell in p.energy:
            if charger_bypass:
                # Concrete omitted-pole countercase: nominal-cap input remains
                # present throughout the rated dump interval.
                inflow=cell.capacity/RESET_REFILL*DUMP_TIME
                loss=min(max(F(0),cell.stock+inflow-DUMP_FLOOR),
                         cell.capacity/DUMP_TIME*DUMP_TIME)
                cell.stock+=inflow-loss;cell.delivered_input+=inflow
                cell.upstream_input+=2*inflow;cell.dumped+=loss
            else:cell.dump(DUMP_TIME)
        if s is not None:
            loss=min(max(F(0),s.energy-DUMP_FLOOR),SET_ENERGY/DUMP_TIME*DUMP_TIME)
            s.energy-=loss
            self.setter_dumped=loss
        self.mark("dumped",DUMP_TIME)
        if any(cell.stock>DUMP_FLOOR for cell in p.energy) or s is not None and s.energy>DUMP_FLOOR:
            return "low-work-guard-not-reached"
        # A corrupt pulse counter cannot veto this separately funded actuator.
        p.flow(F(1000))
        if p.force!=0:
            self.mark("withdrawal-failed",F(1000))
            return "withdrawal-failed"
        self.mark("withdrawn",F(1000))
        self.trigger_aborts=0
        for slot in range(3):
            status=p.abort_pending(slot)
            if status=="aborted":self.trigger_aborts+=1
            elif status!="absent":return status
        # Enumerate fixed reset ports, not an untrusted native program counter.
        # Old write enables remain physically inhibited across the whole sweep.
        need(p.reset_reserve.debit(384) and p.reset_source_reserve.debit(384),
             "Reset fanout work was not separately funded")
        for i in range(1024):
            owner=p.reset_reserve if i<768 else p.reset_source_reserve
            if not owner.debit(2):return "clear-unfunded-wait"
            self.clear_native_bit(i)
        need(p.reset_reserve.debit(1) and p.reset_source_reserve.debit(1),"Reset mode reaction work omitted")
        need(p.slots==[None,None,None],"Bit sweep did not clear actual active registers")
        p.withdrawal_owner=None
        need(all(packet is None for packet in p.pending),"Reset erased an unsettled physical parent")
        if s is not None:
            parent=s.parent_record  # Alias the original immutable parent descriptor.
            self.parent_was_pending=s.phase=="pending"
            self.parent_descriptor_retained=parent
            need(s.reset_reserve.debit(2048),"Setter clear fanout work omitted")
            for i in range(4096):
                if not s.reset_reserve.debit(2):return "setter-clear-unfunded-wait"
                self.setter_bits[i]=0
                if i==0:s.parent_live=False  # Actual native child-valid latch.
            # Partial effects already applied to held[] are deliberately kept.
            s.generator=None
        self.mark("control-cleared",RESET_CLEAR_TIME)
        if s is not None:
            need(s.reset_reserve.debit(1024),"Physical parent-abort work omitted")
            # The fixed old parent receives unavailable and is consumed once;
            # it is not rebound to the next parent or a new body incarnation.
            s.returned=False;s.latched=None;s.parent_record=None;s.phase="recharging"
            need(s.reset_reserve.debit(1),"Setter reset reaction work omitted")
            self.parent_aborted=True
        self.mark("parent-aborted",RESET_ABORT_TIME)
        diverted_interval=DUMP_TIME+1000+RESET_CLEAR_TIME+RESET_ABORT_TIME
        self.pulse_diverted_delivered_heat=3*PULSE_ENERGY/RESET_REFILL*diverted_interval
        self.setter_diverted_delivered_heat=SET_ENERGY/SET_REFILL*diverted_interval if s is not None else F(0)
        self.diverted_delivered_heat=self.pulse_diverted_delivered_heat+self.setter_diverted_delivered_heat
        self.diverted_upstream_work=2*self.diverted_delivered_heat
        self.diverter_conversion_heat=self.diverted_delivered_heat
        # Refill with all trigger/native-write gates still inhibited and the
        # constant clear level still applied. No old count can restart on power.
        p.ep_charging=True;p.refill(RESET_REFILL)
        p.reset_reserve.charge(RESET_REFILL)
        p.reset_source_reserve.charge(RESET_REFILL)
        if s is not None:
            s.recharge(RESET_REFILL);s.reset_reserve.charge(RESET_REFILL)
        self.mark("prepared",RESET_REFILL)
        need(not any(self.native_bits) and not any(self.setter_bits)
             and p.counter_bound_holds() and p.force==0 and all(x.stock==PULSE_ENERGY for x in p.energy)
             and all(x.stock==TRIGGER_ENERGY for x in p.trigger_energy),"Native pool is not actually prepared")
        need(p.cut and p.native_inhibit,"Refill silently re-enabled old authority")
        if s is not None:
            need(s.phase=="ready" and s.energy==SET_ENERGY and s.latched is None,
                 "Setter did not form a real fresh capture state")
            s.native_inhibit=False;s.cut=False  # Fresh scanning is now possible.
        need(self.elapsed==b['prepared_bound'],"Reset episode exceeded its accounted stages")
        return "prepared-trigger-inhibited"

    def enable(self):
        if self.phase!="prepared":return "not-prepared"
        p=self.selector
        need(p.reset_source_reserve.debit(32),"Physical re-enable work omitted")
        p.reset_motor_owner=False;p.native_inhibit=False;p.cut=False
        self.phase="enabled"
        self.events.append(("enabled-after-external-scan",None))
        # This physical action tests no image/vector truth. The programme/cam
        # must put its completed current-C scan before this actual engagement.
        return "enabled"


def rejected(action):
    try:action()
    except ValueError as e:return str(e)
    raise AssertionError("Expected rejection absent")


def local_checks():
    targets = tuple("physical-body-"+str(i) for i in range(DEGREE))
    layout_rejections=[]
    for bad_targets in (targets[:39],targets+("extra",),
                        tuple("physical-body-"+str(i) for i in range(65)),
                        targets[:-1]+(targets[0],),list(targets)):
        layout_rejections.append(rejected(lambda:SettingWriter(bad_targets)))
    fixed=SettingWriter(targets)
    fixed.issue((39,1,L-1,1))
    layout_rejections.append(rejected(lambda:setattr(fixed,'targets',tuple(reversed(targets)))))
    outcomes=[]
    for args, expected in (((0,0,0,1),True),((39,1,L-1,-1),True),
                           ((40,0,0,1),False),((-1,0,0,1),False),
                           ((0,2,0,1),False),((0,0,L,1),False),((0,0,0,2),False)):
        setter=SettingWriter(targets)
        need(setter.issue(args)=="latched", "Missing actual capture")
        need(setter.latched is args,"Setter invented an unpriced pre-copy of parent operands")
        need(setter.issue((1,0,3,0))=="busy", "Occupied setter admitted another parent")
        setter.cut=True  # The paid old setting suffix still completes.
        while setter.phase=="pending":setter.step()
        need(setter.returned==expected and setter.steps==(3615 if expected else 3584)
             and setter.steps<=8192 and setter.energy>1,
             "Native setter bound/outcome failed")
        before=setter.energy
        need(setter.recharge(SET_REFILL,connected=False)=="wait" and setter.energy==before,
             "Disconnected charger invented work")
        need(setter.recharge(SET_REFILL)=="done", "Funded setter did not refill")
        need(setter.issue((0,0,0,1))=="cut", "Post-cut setter renewed old authority")
        outcomes.append(dict(arguments=args,accepted=expected,microsteps=setter.steps,
                             actual_writes=len(setter.held),postwork_energy=before))
    setter=SettingWriter(targets,energy=SET_ENERGY-1)
    need(setter.issue((0,0,0,1))=="unfunded", "Under-reserved setter admitted")
    stalled=SettingWriter(targets)
    need(stalled.issue((0,0,0,1))=="latched","Missing pending wait fixture")
    stalled.step()
    # This starts after an external accounted loss in an affected parent;
    # the local test checks that the partial operation spends no further work.
    stalled.energy=F(17)
    before=(stalled.steps,stalled.logical_cost,stalled.latched,dict(stalled.held),stalled.energy)
    for _ in range(3):
        need(stalled.step()=="unfunded-wait","Unfunded pending operation halted or executed")
    after=(stalled.steps,stalled.logical_cost,stalled.latched,dict(stalled.held),stalled.energy)
    need(after==before and stalled.phase=="pending","Clock-gated wait lost partial state/work")
    need(stalled.issue((1,1,1,-1))=="busy","A new parent replaced unfunded pending work")
    need(8192/SET_CLOCK+SET_REFILL==F(1,64), "Setter nominal suffix changed")
    words=[]
    for word in (0,2**192-1,sum(1<<i for i in range(0,192,2))):
        initial=[F(1-2*((word>>i)&1)) for i in range(192)]
        parent=WorkCell(WORD_ENERGY,WORD_ENERGY)
        cells,steps,work,accepted=native_word(initial,word,parent=parent)
        read=sum(int(x>=0)<<i for i,x in enumerate(cells))
        need(accepted and read==word, "Actual bit endpoints differ from latched word")
        need(parent.spent==16641 and parent.stock==3839,"Native word escaped its actual parent debit")
        repeat=native_word(cells,0,parent=parent)
        need(not repeat[3] and repeat[1]==0,"Native call created a fresh work budget")
        words.append(dict(word=str(word),microsteps=steps,bit_work=work,parent_spent=parent.spent))
    for address in (8192,WORD_MASK):
        cells,steps,work,accepted=native_word([F(-1)]*192,0,address=address,
                                            parent=WorkCell(WORD_ENERGY,WORD_ENERGY))
        need(not accepted and steps==512 and work==0 and cells==[F(-1)]*192,
             "Native invalid address did not reject without a write")
    wire_rejections=[rejected(lambda a=a:native_word([F(-1)]*192,0,address=a,
                                                    parent=WorkCell(WORD_ENERGY,WORD_ENERGY)))
                     for a in (-1,-2**256,2**256,True,0.0)]
    cells,_,_,accepted=native_word([F(-1)]*192,2**220+7,
                                  parent=WorkCell(WORD_ENERGY,WORD_ENERGY))
    need(accepted and sum(int(x>=0)<<i for i,x in enumerate(cells))==7,
         "Native word did not preserve actual192-bit operand masking")
    # Slow writing cannot be treated as the native ISA overwrite mechanism.
    need(bit_flow(-1,Z_MAX,0,F(1,2**26))<0, "Slow/native mobility distinction vanished")
    # Closed threshold contact blocks external fields; actual native writes remain.
    need(bit_flow(F(-1),Z_MAX,0,F(10**20),open_contact=False)==-1,
         "Closed contact leaked external write")
    cell=bit_flow(-1,(F(34)-F(6)*F(202,100)-F(25,100)-F(34,100))*U_BIT,
                  0,F(2)/(F(829,100)*U_BIT))
    need(cell==1, "Threshold write interval did not form endpoint")
    selector=DiagnosticPulseSelector(fixture_edges=2)
    for slot in range(3):need(selector.trigger(slot,-1 if slot==0 else 1)=="active", "Slot failed")
    selector.trigger_energy[0].charge(RESET_REFILL)
    need(selector.trigger(0,1)=="busy", "Occupied pulse timer reset")
    need(selector.selected()==-1, "Old priority was forgotten")
    need(abs(selector.flow(1000))<=FORCE, "Q capsules became Q motors")
    selector.clock_edge(0);selector.clock_edge(0)
    need(selector.selected()==1, "Old expiry zeroed a newer pulse")
    selector.refill(RESET_REFILL)
    need(selector.capture(0,-1)=="latched", "Old trigger was not actually captured")
    selector.cut=True
    need(selector.trigger(0,-1)=="cut", "Cut sampler could retrigger")
    need(selector.deliver(0)=="active", "Paid parent tail erased")
    need(selector.deliver(0)=="absent", "One-shot parent replayed")
    late=DiagnosticPulseSelector()
    late.capture(0,-1)
    need(late.deliver(0,now=F(2))=="expired" and late.selected()==0,
         "Late pending trigger silently renewed old authority")
    need(abs(selector.flow(1000,mode="wrong"))<=FORCE and abs(selector.flow(1000,mode="jam"))<=FORCE,
         "Wrong/jammed output exceeded rated force")
    empty=DiagnosticPulseSelector(slots=[[1,2],None,None],initial_energy=(F(0),F(0),F(0)))
    need(empty.flow(1)==0 and sum(cell.spent for cell in empty.energy)==0,
         "Empty converter created mechanical work")
    powered=PulseSelector(slots=[[1,PULSE_EDGES],None,None],force=U_BIT)
    before=powered.energy[0].stock
    powered.flow(1/BIT_SPEED,relative_velocity=BIT_SPEED)
    need(powered.motor_output>0 and powered.energy[0].stock<before
         and powered.motor_input==powered.motor_output+powered.motor_heat,
         "Physical bit/port work was not debited from the selected capsule")
    repeated_initial=[1,10]
    distinct=PulseSelector(slots=[repeated_initial,repeated_initial,None])
    distinct.clock_edge(0)
    need(distinct.slots[0]==[1,9] and distinct.slots[1]==[1,10]
         and repeated_initial==[1,10],"Initial aliases merged physical slot counters")
    hardware=PulseSelector()
    need(hardware.trigger(0,-1)=="active" and hardware.slots[0][1]==PULSE_EDGES,
         "Ordinary hardware trigger changed its fixed lifetime")
    pulse_rejections=0
    for slot,value in ((True,1),(-1,1),(3,1),(0,True),(0,2)):
        need(hardware.capture(slot,value)=="reject","Malformed pulse payload admitted")
        pulse_rejections+=1
    for slot in (-1,3,True,0.0):
        need(hardware.clock_edge(slot)=="reject" and hardware.deliver(slot)=="reject",
             "Out-of-range native slot accessed state")
        pulse_rejections+=1
    need(hardware.fault_counter(0,PULSE_COUNTER_CAP+1)=="reject",
         "Physical counter mutation escaped installed width")
    hardware.fault_counter(0,PULSE_COUNTER_CAP)
    need(not hardware.counter_bound_holds(),"Arbitrary22-bit state was treated as nominal entry")
    hardware.clock_edge(0)
    need(hardware.slots[0][1]==PULSE_COUNTER_CAP-1 and not hardware.counter_bound_holds(),
         "Clock edge silently reset a corrupt counter to its nominal value")
    initial=PulseSelector(slots=[[1,PULSE_COUNTER_CAP],None,None])
    need(not initial.counter_bound_holds(),"Constructor supplied an initially clean counter")
    high_profile=F(2**16)+16*PULSE_COUNTER_CAP+8*(1+PULSE_COUNTER_CAP+1000)
    need(high_profile+1>2**26,"Arbitrary counter lost its funding obstruction")
    fixture_rejections=[rejected(lambda e=e:DiagnosticPulseSelector(fixture_edges=e))
                        for e in (0,True,PULSE_COUNTER_CAP+1)]
    pair=converter_pair(FORCE,1,(F(1,2),F(-1,4),F(1,4)),(22,3,F(11,10)))
    bad_column=rejected(lambda:converter_pair(FORCE,1,(1,1),(1,1)))
    # Recipient velocity is D*i: replacing it by i misses real work.
    correct=converter_pair(FORCE,0,(F(1),),(F(22),))[0]
    wrong=-FORCE
    need(correct!=wrong, "D*i/i countercase disappeared")
    counter_cases=0
    for width in (20,21,22):
        for value in sorted({0,1,2**width-1} | {2**i for i in range(width)}):
            result,work,cycles=counter_tick(value,width)
            need(result==max(0,value-1) and work<=15 and cycles==64,
                 "Counter work/native capacity failed")
            counter_cases+=1
    # Narrower primitive oscillator interval pays finite native completion
    # latency while preserving the previously exported [1,1.01] edge bounds.
    raw_min=F(5001,5000);raw_max=F(5049,5000);native_delay=F(64)/SET_CLOCK
    need(1/raw_max-native_delay>F(100,101) and 1/raw_min+native_delay<1,
         "Completed counter edge rate changed")
    clock_cases=[]
    for edges in (2**20,2**21):
        minimum=F(edges-1)/raw_max-native_delay
        maximum=F(edges)/raw_min+2*native_delay
        need(minimum>=F(edges-1)*F(100,101) and maximum<=edges,
             "Setup/reset counter latency omitted")
        clock_cases.append(dict(edges=edges,actual_min=minimum,actual_max=maximum))
    return dict(setter=outcomes,setter_unfunded_rejected=True,setter_suffix=F(1,64),
                setter_layout_rejections=layout_rejections,setter_partial_unfunded_wait_checked=True,
                native_words=words,native_invalid_addresses=2,native_wire_rejections=wire_rejections,
                native_operand_mask_checked=True,
                setter_literal_steps_valid=3615,setter_literal_steps_invalid=3584,
                setter_additional_control_budget=8192-3615,setter_complete_control_bound=8192,
                native_word_literal_steps=2048,native_word_completion_step_allowance=32,
                native_store_tail=F(2080)/WORD_CLOCK,
                native_parent_overhead_integer_budget=3838,
                full_CPU_fetch_decode_return_cost_refinement=False,
                motor_has_owned_reservoirs=True,flow_accepts_no_fresh_energy_argument=True,
                nominal_P_does_not_execute_STOREC=True,
                native_STOREC_exceeds_generic_retirement_interval=F(2080)/WORD_CLOCK>F(1,2**26),
                pulse_counter=dict(hardware_edges=PULSE_EDGES,physical_bits=PULSE_COUNTER_BITS,
                  physical_counter_cap=PULSE_COUNTER_CAP,payload_cannot_choose_count=True,
                  malformed_rejections=pulse_rejections,fixture_rejections=fixture_rejections,
                  diagnostic_fixture_not_hardware=True,distinct_physical_counter_storage=True,
                  arbitrary_entry_qualified=False,
                  arbitrary_cap_profile_work=high_profile,
                  arbitrary_cap_profile_exceeds_existing_reserve=True,
                  physical_reformation_from_arbitrary_counter="paid local episode below; programme/cam and fault-domain embedding remain open"),
                selector_single_motor=True,late_parent_retained=True,
                power_pair_example=pair,invalid_joint_column=bad_column,
                wrong_velocity_countercase=dict(actual=correct,incorrect_i=wrong),
                counter_bit_cases=counter_cases,counter_work_upper=15,
                padded_counter_native_cycles=64,clock_interval_cases=clock_cases,
                native_atomic_ISA_observation_refinement="open beyond blocked local processor fragment")


def reformation_checks():
    targets=tuple("physical-body-"+str(i) for i in range(DEGREE))
    cases=[]
    for initial_stock in (F(0),F(17),PULSE_ENERGY):
        p=PulseSelector(slots=[[1,PULSE_COUNTER_CAP],[-1,PULSE_COUNTER_CAP],None],
                        force=FORCE,initial_energy=(initial_stock,initial_stock,PULSE_ENERGY))
        for slot in range(3):
            need(p.capture(slot,-1)=="latched","Old fixed-destination trigger missing")
            p.trigger_energy[slot].debit(TRIGGER_ENERGY-17)
            need(p.deliver(slot,now=F(2))=="unfunded-pending" and p.pending[slot] is not None,
                 "An unfunded old trigger was erased or treated as a completed flight")
        s=SettingWriter(targets)
        # An already applied partial effect is retained; the next parent is
        # genuinely partway through its counted capture and has lost funding.
        key=Destination(targets[0],0,0);s.held[key]=-1
        old_args=(0,0,1,1)
        need(s.issue(old_args)=="latched","Old child capture missing")
        for _ in range(20):s.step()
        s.energy=F(17)  # An admitted earlier accounted loss, not a reset action.
        before=dict(s.held)
        cells=p.energy+p.trigger_energy+[p.reset_source_reserve,p.reset_reserve,s.reset_reserve]
        need(len({id(x) for x in cells})==len(cells),"Physical reset/work stocks alias")
        initial_stocks=[(x.stock,x.delivered_input,x.spent,x.dumped) for x in cells]
        r=PulseReformation(p,s)
        need(r.run()=="prepared-trigger-inhibited","Corrupt native state did not reform")
        need(s.held==before and r.parent_descriptor_retained is old_args
             and r.parent_aborted and not s.parent_live and s.parent_record is None,
             "Reformation erased a partial effect or rebound its old parent")
        need(p.capture(0,1)=="cut" and p.clock_edge(0)=="inhibited-wait",
             "Refill released old authority")
        fresh=(0,0,1,-1)
        need(s.issue(fresh)=="latched","Fresh scanner cannot use the reformed setter")
        while s.phase=="pending":s.step()
        s.recharge(SET_REFILL)
        fresh_key=Destination(targets[0],0,1)
        need(s.held[fresh_key]==-1,"Old drained parent later overwrote the fresh setting")
        need(r.enable()=="enabled" and p.trigger(0,s.held[fresh_key])=="active",
             "Prepared fixed hardware cannot accept a new pulse")
        p.flow(1000)
        need(p.force==-U_BIT and p.counter_bound_holds(),"Fresh actual setting did not reach the field")
        for cell,(initial,received,spent,dumped) in zip(cells,initial_stocks):
            need(cell.stock==initial+cell.delivered_input-received-(cell.spent-spent)-(cell.dumped-dumped),
                 "Actual reset/pulse stock was created or spent twice")
        cases.append(dict(initial_pulse_stock=initial_stock,prepared_duration_bound=r.elapsed,
             source_reset_spent=p.reset_source_reserve.spent,
             receiver_reset_spent=p.reset_reserve.spent,setter_reset_spent=s.reset_reserve.spent,
             pulse_dumped=sum(x.dumped for x in p.energy),setter_dumped=r.setter_dumped,
             diverted_upstream_work=r.diverted_upstream_work,
             pulse_diverted_delivered_heat=r.pulse_diverted_delivered_heat,
             setter_diverted_delivered_heat=r.setter_diverted_delivered_heat,
             diverted_receiver_or_local_heat=r.diverted_delivered_heat,
             diversion_conversion_heat=r.diverter_conversion_heat,
             motor_energy_balance=p.motor_input-p.motor_output-p.motor_heat,
             held_partial_effect_preserved=True,parent_consumed_once=True,
             depleted_trigger_reservations_aborted=r.trigger_aborts,
             phase_budget_trace=r.events))
        need(cases[-1]['motor_energy_balance']==0,"Motor work/heat lost conservation")
        need(p.reset_source_reserve.spent<RESET_SOURCE_ENERGY
             and p.reset_reserve.spent<RESET_RECEIVER_ENERGY
             and s.reset_reserve.spent<SETTER_RESET_ENERGY,"Reset costs exceed their actual separate stores")
    no_reserve=PulseSelector(slots=[[1,PULSE_COUNTER_CAP],None,None],force=FORCE)
    blocked=PulseReformation(no_reserve)
    need(blocked.run(reset_chargers_connected=False)=="reset-unfunded-wait"
         and not no_reserve.counter_bound_holds() and any(blocked.native_bits),
         "Empty reset work became a clean-reset declaration")
    retry=PulseReformation(no_reserve)
    need(retry.run()=="prepared-trigger-inhibited" and no_reserve.counter_bound_holds(),
         "A later funded episode could not resume from retained failed state")
    bypass=PulseSelector(slots=[[1,PULSE_COUNTER_CAP],None,None],force=FORCE)
    failed=PulseReformation(bypass)
    need(failed.run(charger_bypass=True)=="low-work-guard-not-reached"
         and any(x.stock>DUMP_FLOOR for x in bypass.energy),"Uncut charge feed escaped the drain test")
    jammed=PulseSelector(slots=[[1,PULSE_COUNTER_CAP],None,None],force=FORCE,
                         reset_actuator_failed=True)
    jammed_reset=PulseReformation(jammed)
    need(jammed_reset.run()=="withdrawal-failed" and jammed.force!=0 and any(jammed_reset.native_bits),
         "Failed reset actuator was reported as a completed field withdrawal")
    stale=SettingWriter(targets);old=(0,0,7,1);stale.issue(old)
    for _ in range(20):stale.step()
    stale.energy=F(17)
    # A real later bypass refill, with explicit input work, is insufficient:
    # without the physical abort/clear it revives the old captured continuation.
    refill_work=2*(SET_ENERGY-stale.energy);stale.energy=SET_ENERGY
    while stale.phase=="pending":stale.step()
    need(stale.held[Destination(targets[0],0,7)]==1,"Missing stale-child replay countercase")
    # Reopening a forgotten trigger route still admits old values; reformation
    # does not test truth and cannot excuse such a cutset omission.
    bad_route=PulseSelector();bad_route.cut=True
    need(bad_route.capture(0,-1)=="cut","Normal cut failed")
    bad_route.cut=False
    need(bad_route.trigger(0,-1)=="active","Uncut trigger countercase missing")
    fanout_source=F(255,2)+100;fanout_receiver=F(767,2)+100
    setter_control=F(4095,2)+100+1024
    need(fanout_source<=512 and fanout_receiver<=512 and setter_control<=3200,
         "Reset fanout/branch/control allowance is incomplete")
    return dict(bounds=reformation_bounds(),corrupt_initial_cases=cases,
       finite_reset_overheads=dict(source=fanout_source,receiver=fanout_receiver,
                                  setter=setter_control,scope="fixed fanout nodes plus complete fixed control allowance"),
       no_reset_reserve="actual wait, no clearing; later funded episode succeeds",charger_bypass="low-work guard fails",
       failed_reset_actuator="actual bounded work and nonzero field; no completed reset",
       uncut_trigger="old-valued new pulse remains possible",
       refill_without_abort_upstream_work=refill_work,refill_without_abort_replays_old_setting=True,
       absolute_times_are_analyst_annotations=True,
       full_clock_interleaving_and_hybrid_trace_simulated=False,
       runtime_controller_is_not_given_an_absolute_clock=True,
       programme_or_cam_embedding="open: realize the listed physical input sequence and scan-before-enable order")


def accounting(texts):
    old=json.loads(texts['local-control/port_resource_results.json'])['point']
    runtime=json.loads(texts['local-control/resource_results.json'])['runtime_inventory']
    pulse=json.loads(texts['portability/pulse_results.json'])
    timing=json.loads(texts['portability/publication_timing_results.json'])
    tau=F(2**29);F0=F(2**20+22*2**16);w0=F0/16
    Fn=F0+22*REACTION;wn=Fn/16
    H0=w0*w0*tau/2;Hn=wn*wn*tau/2;Jn=Hn/3
    K=4*DEGREE*L
    reset_reaction=2*K*U_BIT/F(1000)+2*U_BIT/F(1000)
    need(F(202,625)+2*NATIVE_FORCE+reset_reaction<REACTION, "Native/reset reactions omitted")
    driver=1+2*FORCE*(BIT_SPEED+22*wn+F(11,10))
    need(driver<8, "Bit/reaction power exceeds pulse profile")
    native_tail=F(2080)/WORD_CLOCK
    native_mechanical=2*NATIVE_FORCE*(BIT_SPEED+22*wn+F(11,10))*native_tail
    need(2080*8+native_mechanical+1<WORD_ENERGY, "Native word depleted its parent")
    need(F(3)/(F(101,100)*WORD_CLOCK)>2/BIT_SPEED, "Native pulse too short at arbitrary phase")
    clear=wn/F(2**15)+(F(4401,100)+REACTION)/32
    need(clear<16 and F(55,2)+REACTION<28 and 68-(F(55,2)+REACTION)-29>0,
         "Clearance or pose progress failed")
    rho=(2**20+22*wn)/(128*tau)
    need(rho<F(1,10000), "Expanded load drift exceeds publication premise")
    age=F(timing['functional']['full_horizon'])
    need(age==F(36671230749,67108864), "Publication age input changed")
    load=F(3,2)*F(51,100)+rho*age
    gap=F(97,100)-F(1,10)-F(11,400000)*age
    need(load<1 and gap>F(4,5), "Actual functional effect horizon failed")
    Cp=F(pulse['inventory']['capsule_energy_capacity']);Cs=2*SET_ENERGY
    Cr=K*RESET_ENERGY+2*SETTER_RESET_ENERGY
    Ppulse=F(pulse['inventory']['installed_continuous_charger_cap'])
    Pfront=F(2**16)*K*F(101,100);Bfront=2**16*K
    Pset=2*(2*SET_ENERGY/SET_REFILL)
    Preset=2*Cr/RESET_REFILL
    bits=256*(1+3)*K+2**24+64*K+2*512;Phold=F(bits,1024)
    # Only old j/u transducers are billed here; new r work belongs to E_p.
    Pm0=2*w0*F0;Pmn=2*wn*F0;Pj0=w0*w0;Pjn=wn*wn
    extra=Ppulse+Pfront+Pset+Preset+Phold+(Pmn-Pm0)+(Pjn-Pj0)
    removed=F(12800*4096*2**30);removed_capacity=F(12800*4096)
    db=F(old['bank_rate']);dbn=db-removed/2
    D0=F(old['upstream_rate']);Dn=D0-F(41,10)*removed+extra
    b0=F(old['upstream_burst']);bn=b0+Bfront
    U0=F(old['new_upstream_capacity']);C0=F(old['total_nonthermal_inventory_upper'])
    nonU_delta=Cp+Cs+Cr-removed_capacity-removed/2+F(4,3)*(Hn-H0)
    Un=U0-nonU_delta;reserve=Un-bn-2*Dn
    need(Dn<D0 and Un>0 and reserve>1, "No funded unchanged-supply point")
    on=F(runtime['per_bank_on']);off=F(runtime['per_bank_off'])
    Emax=F(runtime['per_bank_capacity']);bb=F(runtime['per_bank_burst'])
    startup=6*dbn-F(20,41)*dbn-bb-on
    continuation=on-bb-F(20,41)*dbn-off
    norearm=on-off-dbn/2;drain=4*off-Emax-dbn/2
    need(min(startup,continuation,norearm,drain)>0, "Downrated transit changed a bank law")
    peak=(Cp+Cs+Cr+F(4,3)*(Hn-H0))*2**31+Pfront+Pset+Preset+Phold
    need(41*peak<2**93 and 4*41*peak<2**94, "Native new profiles exceed proposed raw ratings")
    Pzone=F(2**100+2**94);Czone=41*C0
    world_ratio=F((2**96+2**93)*20,7*2**98)
    side=F(1,100)+F(1,200)*wn/w0
    need(world_ratio<1 and side<F(1,50), "World/side-effect envelope failed")
    return dict(mechanics=dict(field_force_cap=FORCE,field_reaction=F(202,625),
          total_reaction=REACTION,reset_reaction_bound=reset_reaction,
          native_force=NATIVE_FORCE,Fhard=Fn,W_over_tau=wn,
          mechanical_stock=Hn,parameter_stock=Jn,driver_work_rate=driver,
          native_word_mechanical_work_upper=native_mechanical,clearance_W_over_tau=clear,
          load_drift=rho,publication_load_drift_cap=F(1,10000),actual_horizon=age,
          load_upper=load,gap_lower=gap,pose_opposition=F(55,2)+REACTION),
        resources=dict(pulse_stock=Cp,setter_stock=Cs,reset_stock=Cr,new_control_bits=bits,
          pulse_chargers=Ppulse,frontend_slope=Pfront,frontend_burst=Bfront,
          setter_chargers=Pset,reset_chargers=Preset,holding_power=Phold,old_port_mechanical_upstream=Pmn,
          parameter_charger_upstream=Pjn,removed_writer_peak=removed,
          removed_writer_stock=removed_capacity,new_bank_rate=dbn,
          actual_bulk_reduction=F(41,10)*removed,added_rate=extra,
          upstream_rate=Dn,upstream_burst=bn,unchanged_supply_rate=D0,
          upstream_capacity=Un,unchanged_total_host_stock=C0,
          usable_reserve_lower=reserve,startup_margin=startup,
          post_on_margin=continuation,no_rearm_margin=norearm,drain_margin=drain),
        thermal=dict(new_native_peak_fit=peak,host_bag_cover=41,zone_stock=Czone,
          new_world_raw_rating=2**93,new_zone_raw_rating=2**94,
          all_nonbath_rating=Pzone,bath_coefficient=Pzone,thermal_capacity=Czone,
          theta_upper=2,world_flow_ratio_to_old_M=world_ratio,
          side_effect_bound_with_old_normalization=side),
        applicability=dict(native_microprices_are_declared_model_laws=True,
          raw_fault_to_g34_b6_admission=False,source_global_nonblocking=False,
          full_family=False,unchanged_baseline_refinement=False))


def serial(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):serial(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [serial(v) for v in value]
    return value


def generate():
    need(not sys.flags.optimize, "Use unoptimized Python")
    texts,binding=inputs()
    return dict(scope="finite local converter/memory/setting source and conditional exact ledger",
        source_base=BASE,frozen_inputs_sha256_lf=binding,local=local_checks(),
        reformation=reformation_checks(),finite_flight=finite_flight_checks(),
        point=accounting(texts),sources_sha256_lf={name:digest((HERE/name).read_text(encoding='utf-8'))
            for name in ('threshold_field_source.py','THRESHOLD-FIELD-SOURCE.md')},
        unclosed=["complete actor/ISA observation and all-mode hybrid refinement",
          "native word32-step completion and remaining3838-work parent frontend/control refinement",
          "setter4577-step additional fixed control refinement within complete8192 bound",
          "native STOREC timing is not a uniform all-opcode retirement lower rate",
          "programme/cam embedding of the constructed pulse/setter reformation input sequence",
          "actual old-inventory domination after writer/body removal",
          "complete finite native-step/control and parent/storage-identity refinement under declared raw prices",
          "physical placement, all-path source/fault map and limiter admission",
          "new geometry/dwell/formation and common-code startup",
          "joint raw incident support: two paired islands can defeat the old six-token map",
          "recurrent source-to-core assembly and whole-program checks"],
        program_completion=False,source_admission=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true');group.add_argument('--check',action='store_true')
    args=parser.parse_args();result=serial(generate());path=HERE/'threshold_field_source_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Field-source evidence binding differs')
    print('PASS local field-source construction; source admission and recurrent family remain open')


if __name__=='__main__':main()
