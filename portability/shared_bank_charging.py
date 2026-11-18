"""Common-stock charging certificates on intervals of fixed eligibility.

Exact rational endpoints are indexed by integrated bank availability. The
elapsed-time certificate retains logarithms instead of rounding a nearly
empty bank to zero. Charge destinations have unit efficiency on this branch.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import pairwise

import parent_retirement as retirement
import parent_realization as original
import input_lifecycle as inputs


def natural_quantity(value):
    if type(value) not in (int, Q) or value < 0:
        raise ValueError("Expected a nonnegative exact physical quantity")
    return Q(value)


@dataclass(frozen=True)
class Clock:
    """Elapsed time is linear + sum(log(ratio)/rate)."""
    linear: Q
    logarithms: tuple

    def then(self, following):
        terms = dict(self.logarithms)
        for rate, ratio in following.logarithms:
            terms[rate] = terms.get(rate, Q(1)) * ratio
        return Clock(self.linear + following.linear, tuple(sorted(terms.items())))


@dataclass(frozen=True)
class Charge:
    credits: tuple
    retained: Q
    clock: Clock


def closed_segment(stock, deficits, rates, exposure):
    """Unit-efficiency, zero inflow/bleed/other draw; fixed local enables."""
    stock = natural_quantity(stock)
    deficits = tuple(map(natural_quantity, deficits))
    rates = tuple(map(natural_quantity, rates))
    exposure = natural_quantity(exposure)
    if len(deficits) != len(rates):
        raise ValueError("Deficits and rates must name the same ordered ports")

    def credits(at):
        return tuple(min(deficit, rate * at) for deficit, rate in zip(deficits, rates))

    final = credits(exposure)
    retained = stock - sum(final)
    if exposure and (stock == 0 or retained < 0 or (retained == 0 and any(final))):
        raise ValueError("Requested exposure has no finite physical endpoint")

    # Sort cap contacts by the common availability coordinate. Between
    # contacts E(a) is affine, so dt = da/min(1,E(a)) integrates exactly.
    endings = {}
    rate = sum(r for d, r in zip(deficits, rates) if d)
    before = stock
    for deficit, port_rate in zip(deficits, rates):
        if port_rate and 0 < deficit / port_rate < exposure:
            hit = deficit / port_rate
            endings[hit] = endings.get(hit, Q(0)) + port_rate
    cuts = {Q(0), exposure, *endings}
    linear = Q(0)
    terms = {}
    for start, end in pairwise(sorted(cuts)):
        length = end - start
        after = before - rate * length
        if rate == 0:
            linear += length / min(1, before)
        elif after >= 1:
            linear += length
        else:
            high_part = max(Q(0), before - 1) / rate
            linear += high_part
            ratio = min(before, Q(1)) / after
            terms[rate] = terms.get(rate, Q(1)) * ratio
        before = after
        rate -= endings.get(end, 0)
    if before != retained:
        raise AssertionError("Capacity events and destination projections disagree")
    return Charge(final, retained, Clock(linear, tuple(sorted(terms.items()))))


class OperatingBank(original.BankWork, inputs.BankEnergy):
    """One installed source. Untimed parent recharge is unavailable here."""
    def __init__(self, owner, capacity, stock):
        if not (isinstance(owner, tuple) and len(owner) == 2 and
                all(type(k) is int and k >= 0 for k in owner) and owner[1] in (0, 1)):
            raise ValueError("Expected the host and bank within one region")
        if type(capacity) is not int or not 0 <= natural_quantity(stock) <= capacity:
            raise ValueError("Invalid operating stock")
        original.BankWork.__init__(self, capacity, Q(stock))
        self.owner = owner
        # The source-local BankEnergy and routed CPU name the same object.
        self.identity = owner

    @property
    def spent(self):
        """Actual E transfers since construction in this zero-inflow chart."""
        bus = getattr(self, "charging", None)
        return self.supplied + (sum(bus.input_received) if bus is not None else 0)

    def debit(self, amount):
        raise RuntimeError("Use the timed shared bank for source charger draws")

    def charge(self, elapsed, payer):
        raise RuntimeError("External inflow requires its own timed bank flow")

    def dump(self, elapsed):
        raise RuntimeError("Bank drainage requires its own timed bank flow")

    def transfer(self, cell):
        raise RuntimeError("Use the timed charging boundary")


class FramedParent(retirement.RetirableParent):
    def recharge(self):
        # Physical inflow occurs only in JointCharge. Do not create an
        # unclocked transfer when the CPU merely checks availability.
        return (self.powered and not self.recharge_inhibit and not self.cell.busy
                and self.pending is None and self.fabric.token is None
                and self.cell.stock == self.cell.capacity)

    def balance(self):
        self.charging.balance()

class JointCharge:
    """A fixed port inventory on one actual bank. No external supply in this adapter."""

    def __init__(self, bank, parent, data_slots, delta):
        if not isinstance(bank, OperatingBank) or not isinstance(parent, FramedParent):
            raise ValueError("Expected a routed parent with timed recharge")
        if getattr(bank, "charging", None) is not None:
            raise ValueError("Operating bank already attached")
        if parent.bank is not bank:
            raise ValueError("CPU and chargers have different physical banks")
        self.bank = bank
        self.parent = parent
        self.slots = tuple(data_slots)
        if any(slot.body[:2] != bank.owner or slot.body[2:3] not in (("DATA",), ("ADC",))
               for slot in self.slots):
            raise ValueError("Foreign charging destination")
        self.delta = natural_quantity(delta)
        if not self.delta:
            raise ValueError("Charger interval must be positive")
        cells = (parent.cell, *(slot.cell for slot in self.slots))
        if len({id(cell) for cell in cells}) != len(cells):
            raise ValueError("The charger inventory duplicates a receiving cell")
        if any(getattr(cell, "charge_owner", None) is not None for cell in cells):
            raise ValueError("Cell already belongs to a charger inventory")
        self.slot_initial = tuple(cell.stock + cell.spent for cell in cells[1:])
        self.initial_bank = bank.stock
        self.initial_parent_supplied = bank.supplied
        self.input_received = [Q(0) for slot in self.slots]
        if parent.cell.stock or parent.cell.spent or parent.cell.dumped:
            raise ValueError("Attach at an empty initial parent")
        if getattr(parent, "charging", None) is not None:
            raise ValueError("Parent already has a charging boundary")
        for cell in cells:
            cell.charge_owner = self
        bank.charging = self
        parent.charging = self

    def ports(self, source_powered):
        if type(source_powered) is not bool:
            raise ValueError("Physical source contact must be boolean")
        cpu = self.parent
        cpu_open = (cpu.powered and not cpu.recharge_inhibit and cpu.pending is None
                    and cpu.fabric.token is None and not cpu.cell.busy)
        cells = (cpu.cell, *(slot.cell for slot in self.slots))
        rates = [cpu.cell.capacity / (2 * self.delta) if cpu_open else 0]
        for slot in self.slots:
            free = slot.claim is None or not slot.claim.live
            rates.append(slot.cell.capacity / self.delta if source_powered and free else 0)
        if any(not 0 <= cell.stock <= cell.capacity for cell in cells):
            raise ValueError("Receiver outside installed capacity")
        return cells, rates

    def apply_exposure(self, exposure, *, source_powered):
        cells, rates = self.ports(source_powered)
        state = closed_segment(self.bank.stock, [c.capacity - c.stock for c in cells],
                               rates, exposure)
        self.bank.stock = state.retained
        self.parent.cell.stock += state.credits[0]
        self.bank.supplied += state.credits[0]
        for i, (slot, amount) in enumerate(zip(self.slots, state.credits[1:])):
            slot.cell.stock += amount
            slot.cell.received += amount
            self.input_received[i] += amount
        self.balance()
        return state.clock

    def flow_full_delivery(self, duration, *, source_powered):
        duration = natural_quantity(duration)
        cells, rates = self.ports(source_powered)
        gross = sum(min(cell.capacity - cell.stock, rate * duration)
                    for cell, rate in zip(cells, rates))
        if duration == 0 or self.bank.stock == 0 or gross == 0:
            self.balance()
            return Clock(duration, ())
        if self.bank.stock - gross < 1:
            raise ValueError("Use the availability chart for a depleted bank")
        return self.apply_exposure(duration, source_powered=source_powered)

    def balance(self):
        p = self.parent
        parent_received = self.bank.supplied - self.initial_parent_supplied
        if self.bank.stock + parent_received + sum(self.input_received) != self.initial_bank:
            raise AssertionError("Unmatched transfer at the shared operating bank")
        if p.cell.stock + p.cell.spent + p.cell.dumped != parent_received:
            raise AssertionError("Unmatched CPU parcel")
        p.fabric.link_balance()
        for i, slot in enumerate(self.slots):
            if slot.cell.stock + slot.cell.spent != self.slot_initial[i] + self.input_received[i]:
                raise AssertionError("Unmatched input cell transfer")


def source_checks():
    from itertools import product
    import input_lifecycle as inputs

    tested = 0
    for deficits, rates in [
        ((8, 4, 3), (3, 4, 2)), ((0, 2, 2, 1), (7, 2, 2, 1)),
        ((3, 0), (0, 1)), ((), ())
    ]:
        for stock, a, b in product((Q(1, 2), Q(1), Q(5), Q(32)),
                                   (Q(0), Q(1, 8), Q(1), Q(2)),
                                   (Q(0), Q(1, 7), Q(1), Q(2))):
            if stock <= sum(min(d, r*(a+b)) for d, r in zip(deficits, rates)):
                continue
            whole = closed_segment(stock, deficits, rates, a+b)
            first = closed_segment(stock, deficits, rates, a)
            left = [d-v for d, v in zip(deficits, first.credits)]
            second = closed_segment(first.retained, left, rates, b)
            assert first.clock.then(second.clock) == whole.clock
            assert second.retained == whole.retained
            assert tuple(x+y for x,y in zip(first.credits, second.credits)) == whole.credits
            tested += 1

    isa, image, ports_class = retirement.source_inputs()
    bank = OperatingBank((2, 0), 100000, Q(100000))
    source = inputs.LocalSourceBank(2, 0, inputs.SourceWork(2, 1000, 1000))
    assert isinstance(bank, inputs.BankEnergy) and source.begin_entry(bank)
    assert source.energy is bank and source.powered and bank.stock == 100000
    try:
        bank.debit(1)
    except RuntimeError:
        pass
    else:
        raise AssertionError("A source-local debit bypassed the timed shared bank")
    cpu = FramedParent(isa, image, bank=bank)
    cpu.C[0] = isa.encode(isa.LI, 3, 0, 0, 7)
    slots = [inputs.DataSlot((2, 0, "DATA", j), 0) for j in (0, 1)]
    delta = original.DELTA
    joint = JointCharge(bank, cpu, slots, delta)
    assert not cpu.recharge() and not cpu.launch()
    assert joint.flow_full_delivery(delta, source_powered=True) == Clock(delta, ())
    assert cpu.cell.stock == 10240 and all(slot.cell.stock==4096 for slot in slots)
    assert slots[0].offer((0,500)) == "accepted"
    pending = slots[0].claim
    assert joint.flow_full_delivery(delta, source_powered=True) == Clock(delta, ())
    assert cpu.launch() and cpu.complete(ports_class(image)) is True and cpu.R[3] == 7
    assert pending is slots[0].claim and pending.live
    effects = []
    assert slots[0].complete(lambda dst, value: effects.append((dst,value)), pending)
    assert effects == [((2,0,"DATA",0),(0,500))]
    assert not slots[0].complete(lambda *args: effects.append(args),pending)
    before = bank.stock
    cpu.inhibit()
    joint.flow_full_delivery(delta,source_powered=False)
    assert bank.stock == before and slots[0].cell.stock == 0 and cpu.cell.stock == 0
    # Enable just the source charger, leave the CPU cut closed.
    joint.flow_full_delivery(delta,source_powered=True)
    assert bank.stock == before-4096 and slots[0].cell.stock == 4096 and not cpu.launch()
    joint.balance()
    try:
        JointCharge(bank,cpu,slots,delta)
    except ValueError:
        pass
    else:
        raise AssertionError("Duplicate bank attachment")

    empty = OperatingBank((2, 1), 100000, Q(0))
    cold_cpu = FramedParent(isa, image, bank=empty)
    try:
        JointCharge(empty, cold_cpu, slots, delta)
    except ValueError:
        pass
    else:
        raise AssertionError("Foreign destination joined")
    cold_slot = inputs.DataSlot((2,1,"DATA",0), 0)
    cold = JointCharge(empty, cold_cpu, (cold_slot,), delta)
    assert cold.flow_full_delivery(1000, source_powered=True) == Clock(Q(1000), ())
    assert not cold_cpu.recharge() and cold_slot.offer(1) == "unfunded"
    assert bank.supplied == original.PARENT
    # Ending a CPU right does not cancel an independent DATA parcel.
    # Keeping it live across an actual parent cut changes no destination.
    assert slots[1].offer((1,222)) == "accepted"
    child = slots[1].claim
    cpu.inhibit()
    joint.apply_exposure(delta/3, source_powered=False)
    assert slots[1].claim is child and child.live and slots[1].cell.stock == 4096
    assert slots[1].complete(lambda dst,val: effects.append((dst,val)), child)
    assert effects[-1] == ((2,0,"DATA",1),(1,222))
    joint.balance()

    # Low-stock witness at a rational availability, across E=1. The clock
    # value is exact, including the subunit logarithmic part.
    r = 4096/delta
    target_exposure = Q(8191, 2)/(2*r)
    low = closed_segment(4096,(4096,4096),(r,r),target_exposure)
    assert low.retained == Q(1,2) and low.credits == (Q(8191,4),)*2
    assert low.clock == Clock(Q(4095)/(2*r),((2*r,Q(2)),))
    try:
        closed_segment(4096,(4096,4096),(r,r),Q(4096)/(2*r))
    except ValueError:
        pass
    else:
        raise AssertionError("Generic proportional export reached zero at finite time")

    print("Exact exposure/elapsed subdivision checks:", tested)
    print("Routed parent and two DATA cells shared E; remaining stock:", bank.stock)
    print("Low-stock exact elapsed certificate:", low.clock)


if __name__ == "__main__":
    import sys
    if sys.version_info[:2] != (3,12) or not __debug__:
        raise SystemExit("Run unoptimized Python 3.12")
    source_checks()
