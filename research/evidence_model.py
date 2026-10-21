"""Exact rational evidence, interval endorsements, and delayed scalar control.

No solver or numerical integration is used. The finite checks are evidence for this
implementation; EVIDENCE.md proves the parameterized continuous theorem.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction as F
from itertools import combinations, product
import json


ACTORS = (0, 1, 2)
# The same identity owns its sensor and authorizer. These are four JOINT coalitions.
FAULT_FAMILY = (frozenset(),) + tuple(frozenset((i,)) for i in ACTORS)


@dataclass(frozen=True, order=True)
class Interval:
    low: F
    high: F

    def contains(self, x: F) -> bool:
        return self.low <= x <= self.high

    def intersect(self, other: Interval) -> Interval | None:
        lo, hi = max(self.low, other.low), min(self.high, other.high)
        return Interval(lo, hi) if lo <= hi else None


@dataclass(frozen=True)
class Parameters:
    safe: Interval = Interval(F(0), F(4))
    demand: F = F(1)
    hostile: F = F(1, 4)
    capacity: F = F(2)
    error: F = F(1, 4)
    period: F = F(1)
    delay_slots: int = 1

    @property
    def delay(self) -> F:
        return self.delay_slots * self.period

    @property
    def radius(self) -> F:
        return self.error + self.hostile * self.delay

    def validate(self) -> None:
        assert self.period > 0 and self.delay_slots >= 1
        assert self.hostile >= 0 and self.error >= 0
        assert self.demand >= self.hostile
        assert self.capacity >= self.demand + self.hostile
        assert self.safe.high - self.safe.low >= 4 * self.radius + 2 * self.hostile * self.period


@dataclass(frozen=True)
class Segment:
    start: F
    end: F
    control: F


@dataclass(frozen=True)
class Report:
    signer: int
    sampled_at: F
    value: F


@dataclass(frozen=True)
class LocalView:
    """Runtime input: no actual state, actual coalition, or future disturbance."""
    observer: int
    epoch: int
    target_slot: int
    effect_at: F
    round_at: F
    reports: tuple[Report, ...]
    schedule: tuple[Segment, ...]


@dataclass(frozen=True)
class Branch:
    faults: frozenset[int]
    states: Interval


@dataclass(frozen=True)
class Endorsement:
    signer: int
    epoch: int
    target_slot: int
    schedule: tuple[Segment, ...]
    allowed: Interval


@dataclass(frozen=True)
class TimedState:
    time: F
    inventory: F
    pending: tuple[F, ...]
    delivered: F = F(0)
    epoch: int = 0
    slot: int = 0
    past: tuple[Segment, ...] = ()


@dataclass(frozen=True)
class Decision:
    control: F
    support: tuple[int, ...]
    messages: tuple[Endorsement, ...]
    views: tuple[LocalView, ...]


def nominal_integral(schedule: tuple[Segment, ...], start: F, end: F, demand: F) -> F:
    """Require exact coverage: silently dropping a queued/past segment is illegal."""
    assert start <= end
    cursor, total = start, F(0)
    for segment in sorted(schedule, key=lambda s: s.start):
        left, right = max(start, segment.start), min(end, segment.end)
        if left < right:
            assert left == cursor, "gap or overlap in authenticated effect schedule"
            total += (right - left) * (segment.control - demand)
            cursor = right
    assert cursor == end, "schedule does not cover prediction horizon"
    return total


def report_interval(report: Report, view: LocalView, p: Parameters) -> Interval:
    assert report.sampled_at <= view.effect_at
    shift = nominal_integral(view.schedule, report.sampled_at, view.effect_at, p.demand)
    radius = p.error + p.hostile * (view.effect_at - report.sampled_at)
    return Interval(report.value + shift - radius, report.value + shift + radius)


def infer_branches(view: LocalView, p: Parameters,
                   family=FAULT_FAMILY) -> tuple[Branch, ...]:
    # None means the universal constraint, not evidence of zero. Missing/invalid
    # faulty packets must not terminate the correct policy. Inputs are attributed
    # structured packets; byte-level parsing and cryptography are outside this model.
    constraints = {i: None for i in ACTORS}
    seen = set()
    for report in view.reports:
        if report.signer not in ACTORS or report.signer in seen:
            continue
        seen.add(report.signer)
        if (not isinstance(report.sampled_at,F) or not isinstance(report.value,F)
                or report.sampled_at < 0 or report.sampled_at > view.round_at):
            continue
        try:
            constraints[report.signer] = report_interval(report, view, p)
        except AssertionError:
            pass  # An unavailable/gapped past schedule licenses no prediction.
    branches = []
    for faults in family:
        state_set = p.safe
        for identity in ACTORS:
            if identity not in faults and constraints[identity] is not None:
                state_set = state_set.intersect(constraints[identity])
                if state_set is None:
                    break
        if state_set is not None:
            branches.append(Branch(faults, state_set))
    return tuple(branches)


def certificate(envelope: Interval, p: Parameters) -> Interval | None:
    return Interval(F(0), p.capacity).intersect(Interval(
        p.demand + p.hostile + (p.safe.low - envelope.low) / p.period,
        p.demand - p.hostile + (p.safe.high - envelope.high) / p.period))


def local_policy(view: LocalView, p: Parameters, family=FAULT_FAMILY) -> Endorsement | None:
    branches = infer_branches(view, p, family)
    if not branches:
        return None  # Inconsistent evidence is not used as a vacuous certificate.
    hull = Interval(min(b.states.low for b in branches), max(b.states.high for b in branches))
    allowed = certificate(hull, p)
    if allowed is None:
        return None
    return Endorsement(view.observer, view.epoch, view.target_slot, view.schedule, allowed)


def gate_select(messages: tuple[Endorsement, ...], epoch: int, target_slot: int,
                schedule: tuple[Segment, ...], p: Parameters) -> tuple[F, tuple[int, ...]]:
    """Authentication is an ideal input-channel condition, not implemented crypto.
    Repeated identities do not add shares. A differing epoch/slot/FIFO is rejected.
    """
    accepted = {}
    for message in messages:
        if (message.signer not in ACTORS or message.signer in accepted
                or message.epoch != epoch or message.target_slot != target_slot
                or message.schedule != schedule):
            continue
        allowed = message.allowed.intersect(Interval(F(0), p.capacity))
        if allowed is not None:
            accepted[message.signer] = allowed
    candidates = []
    for support in combinations(sorted(accepted), 2):
        allowed = accepted[support[0]].intersect(accepted[support[1]])
        if allowed is not None:
            candidates.append((allowed.low, support))
    if not candidates:
        raise ValueError("no available authorized interval")
    return min(candidates)


def schedule_of(state: TimedState, p: Parameters) -> tuple[Segment, ...]:
    assert len(state.pending) == p.delay_slots
    return tuple(Segment(state.time + j*p.period, state.time + (j+1)*p.period, u)
                 for j, u in enumerate(state.pending))


def observe(state: TimedState, observer: int, reported: tuple[F, ...],
            p: Parameters) -> LocalView:
    """Observation map receives externally generated reports; hides inventory/B."""
    return LocalView(observer, state.epoch, state.slot + p.delay_slots,
                     state.time + p.delay, state.time,
                     tuple(Report(s, state.time, reported[s]) for s in ACTORS),
                     schedule_of(state, p))


def decide(state: TimedState, reports: tuple[tuple[F, ...], ...],
           faults: frozenset[int], byzantine_shares: bool,
           p: Parameters) -> Decision:
    # Faults select which local components follow their policy; they are not policy inputs.
    views = tuple(observe(state, i, reports[i], p) for i in ACTORS)
    messages = []
    for i, view in enumerate(views):
        if i not in faults:
            message = local_policy(view, p)
            assert message is not None
            messages.append(message)
        elif byzantine_shares:
            messages.append(Endorsement(i, view.epoch, view.target_slot,
                                        view.schedule, Interval(F(-100), F(100))))
    command, support = gate_select(tuple(messages), state.epoch,
                                  state.slot + p.delay_slots, schedule_of(state, p), p)
    return Decision(command, support, tuple(messages), views)


def plant_step(state: TimedState, newly_committed: F, disturbance: F,
               p: Parameters) -> TimedState:
    """One rational constant-disturbance trace segment; the proof covers measurable w."""
    assert -p.hostile <= disturbance <= p.hostile
    assert 0 <= newly_committed <= p.capacity
    assert len(state.pending) == p.delay_slots
    applied = state.pending[0]
    end = state.time + p.period
    return TimedState(end, state.inventory + p.period*(applied-p.demand+disturbance),
                      state.pending[1:] + (newly_committed,),
                      state.delivered + p.period*p.demand, state.epoch, state.slot+1,
                      state.past + (Segment(state.time, end, applied),))


def pending_tube(state: TimedState, p: Parameters) -> tuple[Interval, ...]:
    low = high = state.inventory
    tube = [Interval(low, high)]
    for u in state.pending:
        low += p.period * (u-p.demand-p.hostile)
        high += p.period * (u-p.demand+p.hostile)
        tube.append(Interval(low, high))
    return tuple(tube)


def tube_is_safe(tube: tuple[Interval, ...], p: Parameters) -> bool:
    return all(p.safe.contains(i.low) and p.safe.contains(i.high) for i in tube)


def make_reports(x: F, faults: frozenset[int], noise: tuple[F, ...],
                 faulty_values: tuple[F, ...]) -> tuple[tuple[F, ...], ...]:
    return tuple(tuple(faulty_values[i] if s in faults else x+noise[s]
                       for s in ACTORS) for i in ACTORS)


@dataclass(frozen=True)
class SensorWorld:
    target: int
    pose_offset: int
    occluded: bool
    calibrated: bool
    registered: int
    reported: int

    def scene_observation(self) -> int | None:
        return None if self.occluded else self.pose_offset


def witness_effect(world: SensorWorld, inject: int) -> int:
    """One delivered unit, with command alphabet {0,2}; safe inventory is {0,1}."""
    assert inject in (0,1)
    return world.target + 2*inject - 1


def witness_checks() -> dict:
    low = SensorWorld(0, 1, False, True, 1, 1)
    high = SensorWorld(1, 0, False, True, 1, 1)
    bad = SensorWorld(0, 0, False, False, 1, 1)
    assert low.reported == high.reported
    assert {1-w.target for w in (low, high)} == {0, 1}
    assert all(w.scene_observation() == 1-w.target for w in (low, high))
    assert all(0 <= witness_effect(w,w.pose_offset) <= 1 for w in (low,high))
    assert all(any(not 0 <= witness_effect(w,u) <= 1 for w in (low,high)) for u in (0,1))
    assert (bad.reported, bad.registered, bad.scene_observation()) == (
        high.reported, high.registered, high.scene_observation())
    assert bad.target != high.target
    register_zero = SensorWorld(0,0,False,True,0,1)
    assert (register_zero.scene_observation(),register_zero.reported) == (bad.scene_observation(),bad.reported)
    assert register_zero.registered != bad.registered
    # All target values are known, but distinct singleton fault evidence licenses different isolation.
    labelled = ((F(0), frozenset((0,))), (F(0), frozenset((1,))))
    assert len({x for x, _ in labelled}) == 1
    assert len({next(iter(b)) for _, b in labelled}) == 2
    # These actual reports operationally rule out no-fault, but support two fault identities.
    p = Parameters()
    disagreement_view = LocalView(2, 0, 0, F(0), F(0),
        (Report(0,F(0),F(0)), Report(1,F(0),F(1)), Report(2,F(0),F(1,2))), ())
    disagreement = infer_branches(disagreement_view, p)
    assert {b.faults for b in disagreement} == {frozenset((0,)),frozenset((1,))}
    assert {b.states for b in disagreement} == {Interval(F(1,4),F(1,4)),Interval(F(3,4),F(3,4))}
    assert not set.intersection(*(set(b.faults) for b in disagreement))
    chosen = F(5,4)
    assert all(certificate(b.states,p).contains(chosen) for b in disagreement)
    # Honest-looking reports admit both no-fault and silent-fault worlds.
    plausible = replace(disagreement_view, reports=tuple(Report(i,F(0),F(1)) for i in ACTORS))
    assert {b.faults for b in infer_branches(plausible,p)} == set(FAULT_FAMILY)
    # Reliable broadcast can prevent recipient-dependent packets while carrying a false value.
    broadcast_attack = make_reports(F(1),frozenset((0,)),(F(0),)*3,(F(8),)*3)
    assert len({row[0] for row in broadcast_attack}) == 1 and broadcast_attack[0][0] != F(1)
    return {"pose_changes_control": True, "pose_does_not_attest_calibration": True,
            "state_projection_loses_isolation": True, "detection_not_attribution": True,
            "decision_without_state_or_fault_identification": True,
            "external_scene_and_report_do_not_identify_register": True,
            "broadcast_prevents_equivocation_not_falsehood": True}


def run_trace(steps: int = 8, p: Parameters = Parameters()) -> list[dict]:
    p.validate()
    state = TimedState(F(0), (p.safe.low+p.safe.high)/2,
                       (p.demand,)*p.delay_slots)
    faults = frozenset((0,))  # One actor controls both the corrupt sensor and authorizer.
    records = []
    for k in range(steps):
        noise = (F(0), p.error if k%2 else -p.error, -p.error if k%2 else p.error)
        reports = make_reports(state.inventory, faults, noise, (F(-8), F(8), F(-8)))
        decision = decide(state, reports, faults, bool(k%2), p)
        disturbance = p.hostile if k%3 else -p.hostile
        nxt = plant_step(state, decision.control, disturbance, p)
        assert tube_is_safe(pending_tube(nxt, p), p)
        records.append({"time": str(state.time), "state": str(state.inventory),
                        "pending": [str(u) for u in state.pending],
                        "chosen_for_time": str(state.time+p.delay),
                        "new_control": str(decision.control), "support": list(decision.support),
                        "faults": sorted(faults), "disturbance": str(disturbance),
                        "next_state": str(nxt.inventory), "delivered": str(nxt.delivered),
                        "local_reports": [[str(r.value) for r in v.reports] for v in decision.views]})
        state = nxt
    return records


def run_checks() -> dict:
    p = Parameters()
    p.validate()
    witnesses = witness_checks()
    states = decisions = effects = branch_checks = 0
    for x, q in product((F(k, 2) for k in range(9)), (F(k, 2) for k in range(5))):
        state = TimedState(F(0), x, (q,))
        if not tube_is_safe(pending_tube(state, p), p):
            continue
        states += 1
        future = pending_tube(state, p)[-1]
        for bad in ACTORS:
            faults = frozenset((bad,))
            honest = tuple(i for i in ACTORS if i != bad)
            for eps, equivocation, send in product(product((-p.error,p.error), repeat=2),
                                                  product((F(-8),F(0),F(8)), repeat=2),
                                                  (False, True)):
                noise, attack = [F(0)]*3, [F(0)]*3
                for j, i in enumerate(honest):
                    noise[i], attack[i] = eps[j], equivocation[j]
                reports = make_reports(x, faults, tuple(noise), tuple(attack))
                decision = decide(state, reports, faults, send, p)
                decisions += 1
                for i in honest:
                    branches = infer_branches(decision.views[i], p)
                    actual = [b.states for b in branches if b.faults == faults]
                    assert len(actual) == 1
                    for z in (future.low, future.high):
                        assert actual[0].contains(z)
                        for branch in branches:
                            assert z-2*p.radius <= branch.states.low <= branch.states.high <= z+2*p.radius
                            branch_checks += 1
                for w in (-p.hostile, F(0), p.hostile):
                    nxt = plant_step(state, decision.control, w, p)
                    assert tube_is_safe(pending_tube(nxt, p), p)
                    assert nxt.delivered == p.demand*p.period
                    effects += 1
    trace = run_trace()
    longer_delay = Parameters(safe=Interval(F(0), F(8)), delay_slots=2)
    run_trace(10, longer_delay)
    # Authentication freshness and exactly-once identity counting are operational checks.
    state = TimedState(F(0), F(2), (F(1),))
    view = observe(state, 0, (F(2),)*3, p)
    assert view == observe(replace(state,inventory=F(3)), 0, (F(2),)*3, p)
    good = local_policy(view, p)
    assert good is not None
    for corrupt_reports in (view.reports[1:],
                            (Report(0,F(99),F(2)),)+view.reports[1:],
                            (Report(0,F(-1),F(2)),)+view.reports[1:]):
        packets = tuple(local_policy(replace(view,observer=i,reports=corrupt_reports),p) for i in (1,2))
        assert all(packet is not None for packet in packets)
        gate_select(packets,0,1,view.schedule,p)
    for invalid in (replace(good, signer=1, epoch=1), replace(good, signer=1, target_slot=9),
                    replace(good, signer=1, schedule=()), good):
        try:
            gate_select((good, invalid), 0, 1, view.schedule, p)
            raise AssertionError("invalid context or repeated identity produced support")
        except ValueError:
            pass
    # Same state/report/age, different FIFO: neither the predicted state nor safe input is preserved.
    slow = TimedState(F(0), F(1), (F(0),))
    fast = TimedState(F(0), F(1), (F(2),))
    exact = Parameters(hostile=F(0), error=F(0))
    sl = local_policy(observe(slow, 0, (F(1),)*3, exact), exact)
    fa = local_policy(observe(fast, 0, (F(1),)*3, exact), exact)
    assert sl is not None and fa is not None and sl.allowed != fa.allowed
    # A one-unit-old physical reading needs both past realized nominal input and FIFO.
    aged = LocalView(1,0,2,F(2),F(1),tuple(Report(i,F(0),F(2)) for i in ACTORS),
                     (Segment(F(0),F(1),F(1)),Segment(F(1),F(2),F(0))))
    old_report = report_interval(aged.reports[0],aged,p)
    assert old_report == Interval(F(1,4),F(7,4))
    assert old_report.contains(F(1,2)) and old_report.contains(F(1))
    assert local_policy(aged,p) is not None
    assert local_policy(replace(aged,schedule=aged.schedule[1:]),p) is None
    # Real-grid repair: old integer controls have empty overlap; a rational command succeeds.
    old = Parameters(safe=Interval(F(2),F(8)), hostile=F(1), error=F(0))
    left, right = certificate(Interval(F(5,2),F(9,2)), old), certificate(Interval(F(9,2),F(13,2)), old)
    assert left is not None and right is not None
    common = left.intersect(right)
    assert common is not None and common.contains(F(3,2))
    assert not any(common.contains(F(k)) for k in (0,1,2))
    return {"lean_expected_declarations": 19, "witnesses": witnesses,
            "finite_scope": "T=1, delta=1, x/q half-grid, endpoint honest noise, 3 corrupt payloads per honest recipient, 1 joint fault, optional broad corrupt endorsement, 3 disturbances",
            "viable_fifo_states": states, "decisions": decisions, "realized_effects": effects,
            "fault_labelled_branch_checks": branch_checks, "freshness_cases": 4,
            "missing_or_invalid_faulty_reports": 3,
            "age_1_history_prediction_checked": True,
            "delay_1_trace": trace, "delay_2_trace_checked": True,
            "fifo_omission_changes_certificate": True, "rational_grid_repair": "3/2"}


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2, sort_keys=True))
