"""Elapsed-time adapter for a routed CPU, native source and its fixed output leads.

This executable covers held zero-inflow bank segments. It uses the exact
high-stock and stationary charts and the strictly positive partial-stock
exposure chart. It does not round a low-stock logarithmic boundary to a tick.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
import subprocess
from pathlib import Path
from types import MappingProxyType
import argparse
import json
import sys

import input_lifecycle as raw
import parent_realization as parent
import parent_retirement as retirement
import shared_bank_charging as charging

HERE = Path(__file__).resolve().parent
BASE = "747d3f292813da3d7ac5682abbf2e901d7f60fda"
DELTA = parent.DELTA
IO_WORK_BOUND = parent.FRONT + 4096 + 1280


def need(condition, message):
    if not condition:
        raise ValueError(message)


def rx_select(lane):
    """Select this lane's actual installed head at its local start aperture."""
    if lane.rx[608]:
        return "busy"
    if not (lane.write_gate and lane.queue.enabled and lane.decode_control[1]
            and not lane.servicing and not lane.decode_control[0]):
        return "stopped"
    if not 0 < lane.queue.number(9,10) <= 512:
        return "empty"
    if not lane.payer.debit(32):
        return "unfunded"
    lane.queue.set_number(609,9,lane.queue.number(0,9))
    lane.rx[608]=1
    return "selected"


def rx_return(lane):
    """Consume one funded selection. Failed funding retains its physical claim."""
    if not lane.write_gate or not lane.rx[608] or not lane.payer.debit(32):
        return None
    head=lane.queue.number(609,9)
    lane.rx[608]=0
    if head!=lane.queue.number(0,9) or not 0<lane.queue.number(9,10)<=512:
        return "changed-or-empty-head/drop"
    return lane.process_one()


class TimedSource(raw.LocalSourceBank):
    """All actual E transfers enter through the attached JointCharge."""

    def __init__(self, bank, upstream, population=None):
        if not isinstance(bank, charging.OperatingBank):
            raise ValueError("Expected the actual joint operating stock")
        super().__init__(*bank.owner, upstream, population)
        self.operating_bank = bank

    def begin_entry(self, energy):
        if energy is not self.operating_bank:
            raise ValueError("Another E object cannot rearm this source")
        return super().begin_entry(energy)

    def recharge(self, duration):
        raise RuntimeError("The source cannot move E in a private time interval")

    def recharge_elapsed(self):
        # Availability at the current event was settled in the common flow.
        return Q(0)

    def rearm(self, energy=None):
        raise RuntimeError("Present the actual power event, entry steps and timed bus separately")

    def advance_cpu(self, ticks=1):
        raise RuntimeError("CPU retirements are not source or destination clock edges")


def timed_ports(isa):
    class Ports(raw.native_source_ports(isa)):
        def __init__(self, image, source):
            super().__init__(image, source)
            self.retire_notifications = 0

        def advance(self, machine):
            # Parent calls this during commit, before its real work cell
            # is freed. No elapsed time or source callback is hidden here.
            self.retire_notifications += 1

        def elapse(self, duration):
            raise RuntimeError("An elapsed physical interval belongs to the common dispatcher")

    return Ports


@dataclass
class Oscillator:
    period: Q
    due: Q

    @classmethod
    def at_rate(cls, rate, first, lower, upper):
        rate = charging.natural_quantity(rate)
        first = charging.natural_quantity(first)
        need(lower <= rate <= upper and first <= 1 / rate, "Invalid physical clock or phase")
        return cls(1 / rate, first)


_UNSPECIFIED = object()


class NativeClock:
    """Source event interface, including a single optional observed RX lane.

    The clock owner may advance to a boundary, then choose each actual
    simultaneous primitive in the source's allowed order. Other physical
    cuts, faults, and CPU capture/return events are caller-supplied roots.
    """

    def __init__(
        self,
        cpu,
        source,
        *,
        adc_rate=4096,
        adc_first=None,
        tx_base_rate=4096,
        tx_first=None,
        rx_base_rate=4096,
        rx_first=None,
        receipt_clock_specs=None,
        pending_record_delays=None,
        existing_bus=None,
        prior_rx_return=_UNSPECIFIED,
        installed_cut=None,
        external_receivers=False,
    ):
        need(
            isinstance(cpu, charging.FramedParent)
            and isinstance(source, TimedSource)
            and cpu.bank is source.operating_bank,
            "CPU and source need the same timed E",
        )
        need(type(external_receivers) is bool, "Unknown receiver-clock ownership")
        need(external_receivers or len(source.receivers_live) <= 1,
             "Use the keyed receiving product for multiple independent lanes")
        self.cpu = cpu
        self.source = source
        self.installed_lanes = tuple(source.receivers_live.values())
        self.lanes = () if external_receivers else self.installed_lanes
        if external_receivers:
            need(rx_first is None and rx_base_rate == 4096 and prior_rx_return is _UNSPECIFIED,
                 "External receiver clocks retain all RX phases and return choices")
        for lane in self.installed_lanes:
            need(
                lane.payer is source.payer
                and all(c.payer is source.payer for c in lane.captures.values()),
                "A fixed source-owned input requires the same actual raw payer",
            )
        pending_record_delays = {} if pending_record_delays is None else pending_record_delays
        need(
            bool(self.lanes) or not (receipt_clock_specs or pending_record_delays),
            "No installed receiver for these clock or pending service inputs",
        )
        if existing_bus is not None:
            need(
                isinstance(existing_bus, charging.JointCharge)
                and getattr(cpu.bank, "charging", None) is existing_bus
                and getattr(cpu, "charging", None) is existing_bus
                and existing_bus.bank is cpu.bank and existing_bus.parent is cpu
                and source.energy is cpu.bank and existing_bus.delta == DELTA
                and len(existing_bus.slots) == len(source.slots)+1
                and all(a is b for a,b in zip(existing_bus.slots, (*source.slots, source.adc)))
                and all(cell.charge_owner is existing_bus for cell in (cpu.cell, *(s.cell for s in existing_bus.slots))),
                "Paced entry requires the original, complete operating-bank installation",
            )
            need(getattr(existing_bus, "native_dispatch", None) is None,
                 "This operating installation already has an elapsed-time dispatcher")
            need(adc_first is not None and tx_first is not None
                 and (external_receivers or (rx_first is not None and prior_rx_return is not _UNSPECIFIED)),
                 "Supply the actual retained base phases and prior RX return")
            if self.lanes:
                need(receipt_clock_specs is not None and set(receipt_clock_specs) == set(self.lanes[0].records),
                     "An already installed receiver needs every retained record phase")
            existing_bus.balance()
        need(installed_cut is None or (existing_bus is not None and callable(installed_cut)),
             "A complex cut must belong to the existing physical installation")
        self.installed_cut=installed_cut
        self.requires_cut_owner=existing_bus is not None
        self.now = Q(0)  # Elapsed origin of this observation, never a device reset.
        self.clocks = {}
        for name, rate, first in (
            ("ADC", adc_rate, adc_first),
            ("TX", tx_base_rate, tx_first),
            ("RX", rx_base_rate, rx_first),
        ):
            if external_receivers and name == "RX":
                continue
            rate = charging.natural_quantity(rate)
            need(rate > 0, "A running oscillator needs positive rate")
            first = 1 / rate if first is None else first
            self.clocks[name] = Oscillator.at_rate(rate, first, Q(4096), Q(4096 * 101, 100))
        rx_clock = self.clocks.get("RX")
        self.rx_suffix = Q(raw.RX_WORK, raw.RX_POWER)
        if external_receivers:
            self.rx_aperture = None
        elif prior_rx_return is _UNSPECIFIED:
            self.rx_aperture = (rx_clock.due + self.rx_suffix) % rx_clock.period
        else:
            previous = rx_clock.due - rx_clock.period + self.rx_suffix
            if prior_rx_return is None:
                need(previous <= 0, "A future return from the preceding RX edge was dropped")
            else:
                prior_rx_return = charging.natural_quantity(prior_rx_return)
                need(prior_rx_return == previous, "Return does not belong to the preceding RX edge")
            self.rx_aperture = prior_rx_return
        self.read_jobs = {}
        # RX[608] and RX[609:618] are a valid bit and selected physical
        # head inside the existing 8192 raw controller bits. A second
        # aperture of the same RX base clock commits after RX_WORK/RX_POWER.
        if self.lanes:
            lane = self.lanes[0]
            specs = {} if receipt_clock_specs is None else receipt_clock_specs
            need(set(specs) <= set(lane.records), "Receipt clock names an uninstalled record")
            for key, record in lane.records.items():
                rate, first = specs.get(key, (Q(5001, 5000), Q(5000, 5001)))
                self.clocks[("tick", key)] = Oscillator.at_rate(
                    rate, first, Q(5001, 5000), Q(5049, 5000)
                )
            pending = {key for key, record in lane.records.items() if self._needs_service(record)}
            need(set(pending_record_delays) == pending, "Supply actual residual times for old raw jobs")
            for key, delay in pending_record_delays.items():
                delay = charging.natural_quantity(delay)
                need(delay <= raw.RECORD_DELAY, "Old record is outside its physical service slot")
                record = lane.records[key]
                kind = self._selected_service(record)
                self.read_jobs[key] = (delay, kind, record.claim if kind == "tick" else None)
        self.edges = dict.fromkeys(self.clocks, 0)
        self.rx_work = []
        self.retired_flights_count = 0
        # Attach only after the entire requested initial clock/endpoint
        # interface has been validated. An invalid clock cannot strand E.
        self.bus = (existing_bus if existing_bus is not None
                    else charging.JointCharge(cpu.bank, cpu, (*source.slots, source.adc), DELTA))
        self.bus.native_dispatch = self
        # Freeze the physical lookup itself. Existing claim destinations, captures
        # and lane objects keep their identity; this does not copy/reseat any row.
        source.receivers_live = MappingProxyType(source.receivers_live)

    @staticmethod
    def _needs_service(record):
        return bool(
            record.control[record.BUSY] or record.control[record.RECEIPT_VALID] or record.queued_tick
        )

    @staticmethod
    def _selected_service(record):
        if record.control[record.BUSY]:
            return "tick"
        if record.control[record.RECEIPT_VALID]:
            return "receipt"
        if record.queued_tick:
            return "queue"
        return None

    def _arm_record(self, key):
        record = self.lanes[0].records[key]
        kind = self._selected_service(record)
        binding = record.claim if kind == "tick" else None
        if kind is not None and (
            key not in self.read_jobs
            or self.read_jobs[key][1] != kind
            or self.read_jobs[key][2] is not binding
        ):
            delay = Q(0) if kind == "queue" else raw.RECORD_DELAY
            self.read_jobs[key] = (self.now + delay, kind, binding)

    def flight_heads(self):
        # The read-only view retains the original mapping. A historical writer
        # alias or a new physical rewiring root cannot silently retarget a
        # paid arrival in a chart which still claims its old installed family.
        need(len(self.source.receivers_live) == len(self.installed_lanes) and all(
            self.source.receivers_live.get(lane.identity) is lane for lane in self.installed_lanes),
            "The fixed receiving installation changed; re-establish its physical routing")
        # Output lines are FIFO. Choices from distinct lines are independent
        # until the receiving port's actual constraints relate them.
        for branch in self.source.branches:
            if branch.flights:
                yield branch, branch.flights[0]

    def due(self):
        events = [name for name, clock in self.clocks.items() if clock.due == self.now]
        events += [
            ("deliver", b.ordinal, child.physical_slot)
            for b, child in self.flight_heads()
            if child.remaining == 0
        ]
        if self.rx_aperture == self.now:
            events.append("rx-commit")
        events += [("commit", k) for k, v in self.read_jobs.items() if v[0] == self.now]
        return tuple(events)

    def next_boundary(self):
        return min(
            [clock.due for clock in self.clocks.values()]
            + [self.now + child.remaining for _, child in self.flight_heads()]
            + ([self.rx_aperture] if self.rx_aperture is not None else [])
            + [job[0] for job in self.read_jobs.values()]
        )

    def _coast_wires(self, dt):
        # Left-limit flow only. The original source advances work and then
        # dispatches at zero tail. Expose that last operation separately so
        # a simultaneous receive-service or new TX may occur first.
        for branch in self.source.branches:
            if branch.wire_credit < raw.WIRE_BURST:
                branch.wire_credit = min(Q(raw.WIRE_BURST), branch.wire_credit + raw.WIRE_RATE * dt)
            for child in branch.flights:
                need(
                    dt <= child.remaining and child.stock == 512 * child.remaining,
                    "Split at the real flight endpoint",
                )
                consumed = 512 * dt
                child.stock -= consumed
                child.spent += consumed
                child.remaining -= dt
                self.source.flight_heat += consumed

    def advance_to(self, moment):
        moment = charging.natural_quantity(moment)
        need(self.now <= moment <= self.next_boundary(), "Crossed an undispatched physical event")
        dt = moment - self.now
        # All charger rates vanish during a joint physical cut. Independent
        # funded children may still evolve. Balance checked at operation ends.
        for wire in self.source.branches:
            for child in wire.flights:
                need(
                    dt <= child.remaining
                    and child.stock == 512 * child.remaining
                    and wire.flight_cells[child.physical_slot] is child,
                    "Split at retained flight contact before bank flow",
                )
        if self.cpu.powered or self.source.powered:
            self.bus.flow_full_delivery(dt, source_powered=self.source.powered)
        self._coast_wires(dt)
        self.now = moment

    def edge(self, event, next_period=None):
        need(event in self.due(), "No such due physical event")
        if next_period is not None:
            need(event in self.clocks, "Only a native oscillator takes a new physical period")
        if isinstance(event, tuple) and event[0] == "commit":
            key = event[1]
            _, kind, binding = self.read_jobs.pop(key)
            rec = self.lanes[0].records[key]
            can_start = kind != "queue" or (
                rec.lane.write_gate and rec.control[rec.ENABLE] and rec.lane.payer.stock >= 32
            )
            if (
                can_start
                and self._selected_service(rec) == kind
                and (kind != "tick" or rec.claim is binding)
            ):
                rec.service()
            self._arm_record(key)
            if kind == "queue" and key in self.read_jobs and self.read_jobs[key][0] == self.now:
                self.read_jobs[key] = (self.now + raw.RECORD_DELAY, *self.read_jobs[key][1:])
            return
        if isinstance(event, tuple) and event[0] == "deliver":
            _, ordinal, index = event
            branch = self.source.branches[ordinal]
            child = branch.flight_cells[index]
            need(
                child is branch.flights[0] and child.stock == 0 and child.remaining == 0,
                "Arrival changed its paid cell or order",
            )
            child.flow(0, self.source.deliver_symbol)
            need(not child.claim.live, "Arrival did not consume its one-shot")
            self.retired_flights_count += 1
            branch.flight_cells[index] = None
            branch.flights.remove(child)
            return
        if event == "rx-commit":
            need(next_period is None, "The RX return aperture is fixed by its source edge")
            self.rx_aperture = None
        else:
            if next_period is not None:
                bounds = (
                    (Q(5000, 5049), Q(5000, 5001))
                    if isinstance(event, tuple)
                    else (Q(100, 4096 * 101), Q(1, 4096))
                )
                period = charging.natural_quantity(next_period)
                need(bounds[0] <= period <= bounds[1], "Physical clock outran its declared range")
                self.clocks[event].period = period
            self.clocks[event].due += self.clocks[event].period
            self.edges[event] += 1
        if isinstance(event, tuple) and event[0] == "tick":
            key = event[1]
            rec = self.lanes[0].records[key]
            # This paced face preserves an earlier staged receipt, including
            # at a true clock tie where the receipt was selected first.
            if rec.control[rec.RECEIPT_VALID] or rec.control[rec.BUSY]:
                if (
                    not rec.queued_tick
                    and rec.lane.write_gate
                    and rec.control[rec.ENABLE]
                    and rec.lane.payer.debit(32)
                ):
                    rec.queued_tick = True
            else:
                rec.start_tick()
            self._arm_record(key)
        elif event == "ADC":
            self.source.adc_tick()
        elif event == "TX":
            self.source.tx_phase = (self.source.tx_phase + 1) % 4
            if self.source.tx_phase == 0:
                for branch in self.source.branches:
                    branch.tick()
        elif event == "rx-commit":
            for lane in self.lanes:
                result = rx_return(lane)
                if result is not None:
                    self.rx_work.append(result)
                    if result != "changed-or-empty-head/drop":
                        for key in lane.records:
                            self._arm_record(key)
        elif event == "RX":
            self.rx_aperture = self.now + self.rx_suffix
            self.source.rx_phase = 1 - self.source.rx_phase
            if self.source.rx_phase == 0:
                for lane in self.lanes:
                    self.rx_work.append(rx_select(lane))

    def run_before(self, moment, choose):
        """Resolve earlier native/arrival events; leave endpoint ties to caller."""
        moment = charging.natural_quantity(moment)
        while self.next_boundary() < moment:
            self.advance_to(self.next_boundary())
            while self.due():
                self.edge(choose(self.due()))
        self.advance_to(moment)

    def stage_receipt(self, key, value):
        record = self.lanes[0].records[key]
        result = record.stage_receipt(value)
        self._arm_record(key)
        return result

    def cut(self):
        if self.installed_cut is not None:
            return self.installed_cut()
        need(not self.requires_cut_owner, "Supply the physical gate for this installed clock's cut")
        self.cpu.inhibit()
        self.source.cold_cut()

    def end_check(self):
        self.bus.balance()
        need(self.cpu.bank is self.source.operating_bank, "Operating source changed")


class OrdinaryCycle:
    """One ordinary clock cycle, with separate capture, IO-offer and return cuts.

    The actual stored parent may survive a failed cycle. No new job is
    silently substituted for it on a later clock. Real clocks and faults
    can interleave with each public edge of this interface.
    """

    IO = {
        "source_start_fast",
        "source_start_functional",
        "source_ready",
        "source_offer_fast",
        "source_invalidate",
    }

    def __init__(self, clock, ports, period, phase_durations=None):
        self.period = charging.natural_quantity(period)
        fractions = (Q(1, 4), Q(1, 4), Q(1, 2))
        parts = (
            tuple(f * self.period for f in fractions)
            if phase_durations is None
            else tuple(map(charging.natural_quantity, phase_durations))
        )
        need(
            len(parts) == 3
            and sum(parts) == self.period
            and all(
                f / Q(101 * 2**26, 100) <= length <= f / Q(2**26) for f, length in zip(fractions, parts)
            ),
            "Outside nominal cycle phase bounds",
        )
        self.parts = parts
        need(
            getattr(clock, "active_cycle", None) is None and ports.source is clock.source,
            "Overlapping cycle or foreign port binding",
        )
        self.clock, self.ports = clock, ports
        self.start = clock.now
        self.phase = "charge"
        self.captured = None
        clock.active_cycle = self

    def time(self, numerator, denominator=1):
        fraction = Q(numerator, denominator)
        need(fraction in (Q(1, 4), Q(1, 2), Q(1)), "Unknown cycle edge")
        count = {Q(1, 4): 1, Q(1, 2): 2, Q(1): 3}[fraction]
        return self.start + sum(self.parts[:count])

    def capture(self):
        need(
            self.phase == "charge" and self.clock.now == self.time(1, 4), "No quarter-cycle capture edge"
        )
        cpu = self.clock.cpu
        self.phase = "offer"
        if cpu.pending is None:
            if not cpu.recharge() or not cpu.launch():
                return "unavailable"
        self.captured = cpu.pending
        return "bound"

    def offer(self):
        need(self.phase == "offer" and self.clock.now == self.time(1, 2), "No source offer edge")
        cpu = self.clock.cpu
        self.phase = "return"
        if self.captured is None or self.captured is not cpu.pending:
            return "no-parent"
        info = cpu._io_info()
        if info is None:
            return "no-source-IO"
        if info[0] not in self.IO:
            return "separate-operation"
        if cpu.io_paid:
            return "already-issued"
        result = cpu.complete(self.ports, pause_after_offer=True)
        need(result == "waiting", "A held parent retired at the issue edge")
        return "issued" if cpu.io_paid else "unavailable"

    def retire(self):
        need(self.phase == "return" and self.clock.now == self.time(1), "No physical return edge")
        cpu = self.clock.cpu
        self.phase = "closed"
        self.clock.active_cycle = None
        if self.captured is None or self.captured is not cpu.pending:
            return "no-parent"
        info = cpu._io_info()
        if info is not None and (info[0] not in self.IO or not cpu.io_paid):
            return "waiting"
        code = cpu.isa.decode(self.captured.cell)[0]
        # The separate native and setter profiles require internal events
        # and may live far longer than this ordinary cycle.
        if code == cpu.isa.STOREC or (code == cpu.isa.IO and info is None):
            return "separate-operation"
        return "retired" if cpu.complete(self.ports) is True else "waiting"


def native_fixture(isa, image, high=True, receive=None, stock=None, **clock_options):
    cap = int(Q(parent.cost_bounds()["actual_bank_capacity"]))
    initial = stock if stock is not None else (cap if high else 0)
    E = charging.OperatingBank((2, 0), cap, initial)
    upstream = raw.SourceWork(2, 1 << 60, 1 << 60)
    source = TimedSource(E, upstream)
    need(
        source.reform() == "formed-unpowered"
        and source.begin_entry(E)
        and source.entry_flow(Q(source.ENTRY_WORK, raw.CLEAR_RATE)),
        "Initial source work unavailable",
    )
    cpu = charging.FramedParent(isa, image, bank=E)
    if receive is not None:
        source.attach(receive(source, upstream))
    clock = NativeClock(cpu, source, **clock_options)
    ports = timed_ports(isa)(image, source)
    return clock, cpu, source, ports


def ordinary_rate_checks():
    fastest_period = 1 / Q(101 * 2**26, 100)
    # First quarter charges a completely empty parent. Second quarter is
    # a sufficient allowance for the scoped captured ordinary source offer;
    # the remaining half includes result commit. This is a sufficient
    # constant-rate placement, not an obligation to select identical phases.
    need(2 * DELTA < fastest_period / 4, "Parent cannot fill before capture")
    need(Q(IO_WORK_BOUND) / parent.NATIVE_RATE < fastest_period / 4, "Source offer cannot fit")
    # Charge newly explicit raw clock/selection controls to the source U, at
    # both ends of the same observational boundary, separately from bank E.
    # One RX start and one possible completion per RX base cycle (even a
    # corrupted divider); one queued-tick capture per raw record tick.
    lanes = 160
    records = 320480
    added_burst = 2 * (2 * 32 * lanes + 32 * records)
    added_rate = 2 * (2 * 32 * lanes * (4096 * Q(101, 100)) + 32 * records * Q(101, 100))
    resources = json.loads((HERE / "input_lifecycle_results.json").read_text())["resources"]
    reserve = Q(resources["usable_reserve_lower"]) - added_burst - 2 * added_rate
    need(
        reserve > 1
        and Q(resources["updated_upstream_rate"]) + added_rate < Q(resources["unchanged_supply_rate"]),
        "RX aperture/queued-tick work is unaffordable",
    )
    need(
        64 + 64 + 11584 + 512 <= raw.RX_WORK and Q(raw.RX_WORK, raw.RX_POWER) < Q(1, 4096) * Q(100, 101),
        "RX selection/commit timing invalid",
    )
    return dict(
        fastest_period=fastest_period,
        worst_scoped_offer_work=IO_WORK_BOUND,
        native_work_time=Q(IO_WORK_BOUND) / parent.NATIVE_RATE,
        additional_RX_U_burst=added_burst,
        additional_RX_U_rate=added_rate,
        local_input_inclusive_U_reserve=reserve,
        scope="before B gate/other subsequent additions",
    )


def entry_and_cut(isa, image, cut, adc_first):
    tau = 16 * DELTA
    clock, cpu, source, ports = native_fixture(isa, image, adc_first=tau / 2)
    # Actual changed-image publish_plant PC267 and its real CALL at PC268.
    # The operand state is a scoped routine-prefix fixture.
    cpu.pc = 267
    cpu.R[205] = 0
    cpu.R[1] = 0
    source.raw_heads[0] = 731
    first = isa.decode(image.image[267])
    need(
        first[0] == isa.IO
        and first[-1] == isa.PRIM["source_start_fast"]
        and isa.decode(image.image[268])[0] == isa.CALL,
        "Expected actual publish_plant spine",
    )
    T = lambda t: clock.run_before(t, lambda due: due[0])
    need(not cpu.recharge(), "CPU obtained an untimed empty-slot transfer")
    cycle = OrdinaryCycle(clock, ports, tau)
    T(tau / 4)
    need(cycle.capture() == "bound", "Timed quarter-cycle capture failed")
    need(
        cpu.bank.supplied == 20480 and sum(clock.bus.input_received) == Q(84539311, 2),
        "Actual source and parent did not share the post-dump transfer",
    )
    T(tau / 2)
    if adc_first:
        clock.edge("ADC")
    if cut == "before":
        clock.cut()
    need(cycle.offer() == ("unavailable" if cut == "before" else "issued"), "Unexpected offer result")
    if not adc_first:
        clock.edge("ADC")
    old = source.job
    count = source.adc_bits.get(2052, 6)
    if cut == "after":
        clock.cut()
    stock = cpu.bank.stock
    T(tau)
    outcome = cycle.retire()
    if cut == "none":
        need(
            outcome == "retired" and cpu.pc == 268 and ports.retire_notifications == 1,
            "No genuine first retirement",
        )
        cycle = OrdinaryCycle(clock, ports, tau)
        T(5 * tau / 4)
        need(cycle.capture() == "bound", "Next quarter-cycle did not recharge")
        T(3 * tau / 2)
        need(cycle.offer() == "no-source-IO", "CALL issued another I/O")
        T(2 * tau)
        need(
            cycle.retire() == "retired"
            and cpu.pc == image.labels["wait_conversion"]
            and cpu.W[0] == 269
            and cpu.R[1] == 1
            and cpu.steps == 2
            and source.job is old,
            "Actual CALL changed its caller or the ongoing ADC",
        )
    else:
        need(
            outcome == "waiting" and cpu.steps == 0 and cpu.cell.busy and cpu.pending is not None,
            "Interrupted CPU completion created a return",
        )
        if cut == "before":
            need(old is None and source.samples == 0, "Cut-before-offer launched ADC")
        else:
            need(old is not None and old.live, "Accepted ADC lost its binding")
            for _ in range(count):
                T(clock.clocks["ADC"].due)
                while clock.due():
                    clock.edge(clock.due()[0])
            need(
                source.I[1] == 731 and source.valid and source.adc_completed == 1 and not old.live,
                "Existing ADC did not finish on its independent clock",
            )
            need(
                cpu.steps == 0 and cpu.bank.stock == stock, "Blocked CPU powered a continued conversion"
            )
    clock.end_check()
    return dict(
        cut=cut,
        adc_first=adc_first,
        count_after_tie=count,
        retired=cpu.steps,
        pc=cpu.pc,
        source_conversions=source.adc_completed,
        elapsed=clock.now,
        parent_transfer=cpu.bank.supplied,
        input_transfer=sum(clock.bus.input_received),
    )


def arrival_cut(isa, image, read_first):
    # A real previously emitted symbol at the end of its propagation.
    # The RX clock binds an existing head, then the paid parser completes
    # after its separate native service slot. Endpoint ties remain explicit.
    clock, cpu, source, _ = native_fixture(
        isa, image, receive=lambda src, U: raw.RawLane(src.population, src.branches[0].destination, U)
    )
    # Nonempty source queue at the left endpoint. The initial native charge
    # is an actual timed transfer. Emit on the fourth TX base edge.
    clock.advance_to(2 * DELTA)
    b = source.branches[0]
    need(b.offer(0, 71) == "accepted", "Missing funded source request")
    out_time = Q(1, 1024)
    clock.run_before(out_time, lambda due: due[0])
    while clock.due():
        clock.edge(clock.due()[0])
    need(len(b.flights) == 1, "Actual TX service failed to emit the first symbol")
    child = b.flights[0]
    clock.cut()
    before = cpu.bank.stock
    clock.run_before(out_time + Q(1, 4), lambda due: due[0])
    flight_event = ("deliver", 0, child.physical_slot)
    first, second = ("RX", flight_event) if read_first else (flight_event, "RX")
    clock.edge(first)
    clock.edge(second)
    while clock.due():
        clock.edge(clock.due()[0])
    lane = clock.lanes[0]
    at_tie = lane.queue.number(9, 10)
    need(at_tie == 1 and bool(lane.rx[608]) == (not read_first), "Tied RX chose a future symbol")
    end = clock.now + Q(raw.RX_WORK, raw.RX_POWER)
    clock.run_before(end, lambda due: due[0])
    while clock.due():
        clock.edge(clock.due()[0])
    count = lane.queue.number(9, 10)
    need(
        count == int(read_first)
        and not b.flights
        and not child.claim.live
        and child.stock == 0
        and child.spent == 128
        and cpu.bank.stock == before,
        "RX and arrival ordering or old charge retention was erased",
    )
    clock.end_check()
    return dict(
        read_first=read_first,
        paid_flight=child.spent,
        queued_after_tie=count,
        receiver_result=clock.rx_work[-1],
        source_clock_continued_while_cut=True,
    )


def receipt_order(isa, image, tick_first):
    def make_lane(source, payer):
        return raw.RawLane(source.population, raw.LaneId(2, 0, 0, 0), payer)

    clock, cpu, source, _ = native_fixture(isa, image, receive=make_lane)
    clock.cut()  # Raw receiver work is powered by the actual origin U.
    lane = clock.lanes[0]
    key = next(k for k, r in lane.records.items() if r.lifetime == 8)
    record = lane.records[key]
    record.set_ttl(3)
    record.value = 42
    clock.clocks["tick", key].due = Q(0)
    if tick_first:
        clock.edge(("tick", key))
    need(
        clock.stage_receipt(key, 71) == "staged" and record.readable() == 42,
        "Staging erased the readable old raw word",
    )
    if not tick_first:
        clock.edge(("tick", key))
    first = raw.RECORD_DELAY
    clock.run_before(first, lambda due: due[0])
    clock.edge(("commit", key))
    intermediate = (record.value, record.ttl)
    # If receipt retired first, the old request now captures the NEW value.
    while clock.due():
        clock.edge(clock.due()[0])
    clock.run_before(2 * first, lambda due: due[0])
    while clock.due():
        clock.edge(clock.due()[0])
    need(
        intermediate == ((42, 2) if tick_first else (71, 8))
        and record.value == 71
        and record.ttl == (8 if tick_first else 7),
        "Timed arbitration lost a permitted tick/receipt order",
    )
    clock.end_check()
    return dict(
        tick_first=tick_first,
        intermediate=intermediate,
        final=(record.value, record.ttl),
        clock=clock.now,
        ordinary_bank_cut=True,
    )


def scarce_wait(isa, image):
    no, cpu, src, _ = native_fixture(isa, image, high=False, adc_first=0, tx_first=0, rx_first=0)
    for _ in range(4):
        no.advance_to(no.next_boundary())
        while no.due():
            no.edge(no.due()[-1])
    need(
        not cpu.recharge()
        and not cpu.launch()
        and cpu.steps == 0
        and no.now > 0
        and cpu.bank.stock == 0,
        "Zero-stock waiting stopped physical time or minted an instruction",
    )
    no.end_check()
    # Positive scarce stock moves continuously; it cannot be called stationary.
    # Use a deliberately held low-stock segment of the existing exact chart.
    a = charging.closed_segment(Q(1, 2), (4096, 4096), (1, 1), Q(1, 8))
    need(
        a.credits == (Q(1, 8),) * 2
        and a.retained == Q(1, 4)
        and a.clock == charging.Clock(0, ((2, Q(2)),)),
        "Scarce elapsed chart changed",
    )
    # Even a paid source E connection cannot issue at zero bank stock.
    cyc = OrdinaryCycle(no, timed_ports(isa)(image, src), 16 * DELTA)
    no.run_before(cyc.time(1, 4), lambda ds: ds[0])
    need(cyc.capture() == "unavailable", "Empty parent latched C")
    no.run_before(cyc.time(1, 2), lambda ds: ds[0])
    need(cyc.offer() == "no-parent", "Empty parent offered")
    no.run_before(cyc.time(1), lambda ds: ds[0])
    need(cyc.retire() == "no-parent", "Empty parent retired")
    low, partial, under, _ = native_fixture(isa, image, stock=Q(1, 2))
    cells, rates = low.bus.ports(source_powered=True)
    initial = partial.bank.stock
    need(all(c.capacity - c.stock > initial for c in cells), "Scarcity no-cap reduction unavailable")
    rate = sum(rates)
    # None of these recipients can reach capacity from the whole bank, so
    # their elapsed-time dynamics have one aggregate slope throughout.
    duration = Q(2, 2**26)
    need(duration < low.next_boundary(), "A native event cuts the selected positive-stock wait")
    tol = 1 / (1024 * rate)
    band = charging.exposure_at_time(initial, (initial,), (rate,), duration, tol)
    need(
        0 < band.lower <= band.upper
        and band.upper - band.lower <= tol
        and all(c.stock + min(initial, r * band.upper) < c.capacity for c, r in zip(cells, rates)),
        "Finite real-time interval lacked a separating underfunded certificate",
    )
    # Independent rational Taylor bounds for the tied-cap boundary followed
    # by E=exp(-2*(t-1)); at t=5/4 the exact exponent is -1/2.
    term = Q(1)
    total = Q(1)
    for k in range(1, 18):
        term *= -Q(1, 2 * k)
        total += term
    exp_lower = total
    exp_upper = total + term * (-Q(1, 36))
    chart = charging.exposure_at_time(5, (1, 1, 8), (1, 1, 2), Q(5, 4), Q(1, 10**7))
    need(
        chart.lower <= 1 + (1 - exp_upper) / 2 <= 1 + (1 - exp_lower) / 2 <= chart.upper,
        "Scarce clock enclosure missed independent exponential bounds",
    )
    return dict(
        zero_stock_elapsed=no.now,
        zero_stock_retirements=cpu.steps,
        positive_chart_exposure=Q(1, 8),
        positive_chart_retained=a.retained,
        elapsed_expression="log(2)/2",
        both_underfunded=True,
        positive_E_start=initial,
        positive_wait_duration=duration,
        aggregate_rate=rate,
        availability_bracket=(band.lower, band.upper),
        all_slots_and_CPU_remain_unfunded=True,
        strictly_positive_E_expression="E(0)*exp(-rate*duration)",
        tied_caps_time=Q(5, 4),
        tied_caps_availability=(chart.lower, chart.upper),
    )


def serial(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {k: serial(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serial(v) for v in value]
    return value


def generate():
    need(sys.version_info[:2] == (3, 12) and __debug__, "Unoptimized Python 3.12 required")
    isa, image, _ = retirement.source_inputs()
    names = (
        "NATIVE-CLOCK-SOURCE.md",
        "native_clock_source.py",
        "shared_bank_charging.py",
        "input_lifecycle.py",
        "input_lifecycle_results.json",
        "parent_realization.py",
        "parent_realization_results.json",
        "parent_retirement.py",
        "parent_retirement_results.json",
    )
    bindings = {n: sha256((HERE / n).read_bytes().replace(b"\r\n", b"\n")).hexdigest() for n in names}
    for name in names[2:]:
        old = subprocess.check_output(
            ["git", "show", BASE + ":theories-and-designs/byzantine-control/portability/" + name],
            cwd=HERE,
        )
        need(
            sha256(old.replace(b"\r\n", b"\n")).hexdigest() == bindings[name],
            "Changed bound native-clock input " + name,
        )
    image_digest = retirement.parent.program.hash_text(json.dumps(image.image))
    for name in (
        "input_lifecycle_results.json",
        "parent_retirement_results.json",
        "parent_realization_results.json",
    ):
        record = json.loads((HERE / name).read_text(encoding="utf-8-sig"))
        for source, digest in (
            record.get("immutable_inputs_sha256_lf", {}) | record["sources_sha256_lf"]
        ).items():
            need(
                retirement.parent.program.digest(HERE / source) == digest,
                "Changed supplier source " + source,
            )
        if "image_sha256" in record:
            need(record["image_sha256"] == image_digest, "Paced source compiled a different image")
    return serial(
        dict(
            status="derived scoped elapsed-time source/parent/child comparison",
            base=BASE,
            image=image_digest,
            rates=ordinary_rate_checks(),
            entry_cut=[
                entry_and_cut(isa, image, cut, order)
                for cut in ("none", "after", "before")
                for order in (False, True)
            ],
            arrival_orders=[arrival_cut(isa, image, order) for order in (True, False)],
            receipt_orders=[receipt_order(isa, image, f) for f in (True, False)],
            scarcity=scarce_wait(isa, image),
            sources_sha256_lf=bindings,
            remaining=[
                "complete source-native/receiver interval and intervening fault maps",
                "external inflow, bleed, physical trip and distributed charger composition",
                "all opcodes, setter/native waits, common-history progress and held-out transfer",
            ],
            full_timed_ISA=False,
            whole_family_admitted=False,
            program_completion=False,
        )
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = generate()
    path = HERE / "native_clock_source_results.json"
    if args.write:
        path.write_text(
            json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n"
        )
    else:
        need(result == json.loads(path.read_text(encoding="utf-8")), "Native clock record differs")
    print("PASS scoped common-bank and independent-clock transitions; full physical source remains open")


if __name__ == "__main__":
    main()
