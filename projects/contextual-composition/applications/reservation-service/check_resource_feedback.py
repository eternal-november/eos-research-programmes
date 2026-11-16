"""Exact finite checks for a recurrent, reusable named resource pool.

Only stdlib; no output files. Run without -O. The semantic rules have no bound
on generations. Exhaustive exploration restricts Submit to two generations
per client solely to obtain a finite diagnostic graph. A separate prefix uses
the unrestricted rules past that bound. These checks are not an infinite-run
proof or an implementation bridge to the full occurrence runtime.

Two concrete allocation policies (uniform free unit, first fit) refine one
reference retaining the available count AND logical reservation/receipt data.
Only opaque homogeneous unit placement is forgotten. All other step rules are
the shared declared service specification; the checks do not claim independent
implementation verification of those common logical rules.
"""

from collections import defaultdict, deque
from dataclasses import dataclass, replace
from fractions import Fraction as F
import json


RESOURCE = "pool-rho"
PHASE_RANK = {"RESERVED": 4, "APPLIED": 3, "NOTIFIED": 2, "COOLING": 1}


@dataclass(frozen=True, order=True)
class Reservation:
    rid: tuple
    owner: int
    unit: int | None
    phase: str


@dataclass(frozen=True)
class State:
    capacity: int
    resource: str
    up: bool
    free: tuple | int
    reservations: tuple
    queue: tuple
    acks: tuple
    applied: tuple
    receipts: tuple
    clients: tuple
    generation: tuple
    cost: int


@dataclass(frozen=True)
class Outcome:
    raw: object
    weight: F
    state: State
    event: tuple


def initial(capacity, clients=2, concrete=True):
    return State(capacity, RESOURCE, True, tuple(range(capacity)) if concrete else capacity,
                 (), (), tuple(() for _ in range(clients)), (), (),
                 tuple(None for _ in range(clients)), tuple(0 for _ in range(clients)), 0)


def available(state):
    return len(state.free) if isinstance(state.free, tuple) else state.free


def abstract(state):
    return replace(state, free=available(state),
                   reservations=tuple(replace(record, unit=None) for record in state.reservations))


def record_map(state):
    return {record.rid: record for record in state.reservations}


def with_record(state, record):
    records = record_map(state)
    records[record.rid] = record
    return replace(state, reservations=tuple(sorted(records.values())))


def tuple_at(values, index, value):
    result = list(values)
    result[index] = value
    return tuple(result)


def add_id(values, rid):
    return tuple(sorted(set(values) | {rid}))


def invariant(state):
    count = len(state.clients)
    assert state.resource == RESOURCE and state.capacity >= 0
    assert len(state.acks) == len(state.generation) == count
    assert all(n >= 0 for n in state.generation)
    records = record_map(state)
    assert len(records) == len(state.reservations)
    assert len(set(state.queue)) == len(state.queue)
    assert not set(state.queue) & set(records)
    assert tuple(sorted(set(state.applied))) == state.applied
    assert tuple(sorted(set(state.receipts))) == state.receipts
    assert set(state.receipts) <= set(state.applied)
    assert state.cost == len(state.applied)
    issued = {(owner, generation) for owner, limit in enumerate(state.generation)
              for generation in range(limit)}
    assert set(state.queue) | set(records) | set(state.receipts) == issued
    assert set(state.applied) <= issued
    assert available(state) + len(records) == state.capacity
    assert 0 <= available(state) <= state.capacity
    if isinstance(state.free, tuple):
        units = [record.unit for record in records.values()]
        assert len(set(units)) == len(units)
        assert len(set(state.free)) == len(state.free)
        assert not set(units) & set(state.free)
        assert set(units) | set(state.free) == set(range(state.capacity))
    else:
        assert all(record.unit is None for record in records.values())
    for rid in state.queue:
        owner, _ = rid
        assert state.clients[owner] == rid and rid not in state.applied
    for rid, record in records.items():
        assert 0 <= record.owner < count and record.owner == rid[0]
        assert record.phase in PHASE_RANK
        if record.phase == "RESERVED":
            assert rid not in state.applied and rid not in state.receipts
        else:
            assert rid in state.applied
        if record.phase == "COOLING":
            assert rid in state.receipts and state.clients[record.owner] != rid
        else:
            assert state.clients[record.owner] == rid and rid not in state.receipts
        assert (rid in state.acks[record.owner]) == (record.phase == "NOTIFIED")
    for owner, ack_queue in enumerate(state.acks):
        assert len(ack_queue) <= 1  # One outstanding request per client.
        for rid in ack_queue:
            assert records[rid].owner == owner and records[rid].phase == "NOTIFIED"
        rid = state.clients[owner]
        if rid is not None:
            assert rid[0] == owner and (rid in state.queue or rid in records)
            if rid in records:
                assert records[rid].phase != "COOLING"
    # In this model E has a redundant reconstruction, so a necessity claim
    # about storing this exact field would be stronger than the evidence.
    reconstructed = set(state.receipts) | {rid for rid, record in records.items()
                                         if record.phase != "RESERVED"}
    assert reconstructed == set(state.applied)
    return True


def ready(state, generation_limit=None):
    actions = []
    for owner, pending in enumerate(state.clients):
        if pending is None and (generation_limit is None or state.generation[owner] < generation_limit):
            actions.append(("Submit", owner))
    if state.up and available(state) and state.queue:
        actions.append(("Reserve", state.queue[0]))
    for record in state.reservations:
        if record.phase == "RESERVED" and state.up:
            actions.append(("Apply", record.rid))
        if record.phase == "APPLIED":
            actions.append(("Publish", record.rid))
        if record.phase == "COOLING" and state.up:
            actions.append(("Clean", record.rid))
    for owner, ack_queue in enumerate(state.acks):
        if ack_queue:
            actions.append(("Deliver", ack_queue[0]))
    return tuple(sorted(actions))


def event(state, name, *fields):
    return (name, state.resource, *fields)


def singleton(state, label):
    return (Outcome(None, F(1), state, label),)


def refusal(state, reason, resource, owner, rid):
    return singleton(state, ("Refusal", resource, owner, rid, reason))


def transition(state, action, allocation="uniform"):
    """The unbounded local rules; no generation/exploration bound is read."""
    name = action[0]
    records = record_map(state)
    if name == "Tick":
        return singleton(state, event(state, "Tick"))
    if name == "Down":
        assert state.up
        return singleton(replace(state, up=False), event(state, "Down"))
    if name == "Up":
        assert not state.up
        return singleton(replace(state, up=True), event(state, "Up"))
    if name in ("Probe", "Retry"):
        _, resource, owner, rid = action
        if resource != state.resource:
            return refusal(state, "wrong-resource", resource, owner, rid)
        if not (0 <= owner < len(state.clients)) or rid[0] != owner:
            return refusal(state, "wrong-owner", resource, owner, rid)
        if not (0 <= rid[1] < state.generation[owner]):
            return refusal(state, "unknown-request", resource, owner, rid)
        if name == "Probe":
            status = records[rid].phase if rid in records else ("QUEUED" if rid in state.queue else "RETIRED")
            return singleton(state, event(state, "Status", owner, rid, status, available(state)))
        if rid in state.applied:
            return singleton(state, event(state, "AlreadyApplied", owner, rid))
        if rid in records and records[rid].phase == "RESERVED" and state.up:
            return transition(state, ("Apply", rid), allocation)
        return refusal(state, "not-ready", resource, owner, rid)
    if name == "Apply" and action[1] in state.applied:
        rid = action[1]
        return singleton(state, event(state, "AlreadyApplied", rid[0], rid))
    assert action in ready(state), (state, action)
    if name == "Submit":
        owner = action[1]
        rid = owner, state.generation[owner]
        after = replace(state, queue=state.queue + (rid,),
                        clients=tuple_at(state.clients, owner, rid),
                        generation=tuple_at(state.generation, owner, rid[1] + 1))
        return singleton(after, event(state, "Submitted", owner, rid))
    rid = action[1]
    if name == "Reserve":
        assert state.queue[0] == rid and state.up
        if isinstance(state.free, int):
            choices = (None,)
        elif allocation == "uniform":
            choices = state.free
        else:
            assert allocation == "first_fit"
            choices = (min(state.free),)
        outcomes = []
        for unit in choices:
            remaining = state.free - 1 if isinstance(state.free, int) else tuple(u for u in state.free if u != unit)
            after = replace(state, queue=state.queue[1:], free=remaining)
            after = with_record(after, Reservation(rid, rid[0], unit, "RESERVED"))
            outcomes.append(Outcome(unit, F(1, len(choices)), after,
                                    event(state, "Reserved", rid[0], rid)))
        return tuple(outcomes)
    record = records[rid]
    if name == "Apply":
        assert state.up and record.phase == "RESERVED"
        after = with_record(state, replace(record, phase="APPLIED"))
        after = replace(after, applied=add_id(state.applied, rid), cost=state.cost + 1)
        return singleton(after, event(state, "Applied", record.owner, rid))
    if name == "Publish":
        assert record.phase == "APPLIED"
        after = with_record(state, replace(record, phase="NOTIFIED"))
        after = replace(after, acks=tuple_at(state.acks, record.owner, state.acks[record.owner] + (rid,)))
        return singleton(after, event(state, "AckQueued", record.owner, rid))
    if name == "Deliver":
        assert state.acks[record.owner][0] == rid and record.phase == "NOTIFIED"
        after = with_record(state, replace(record, phase="COOLING"))
        after = replace(after, acks=tuple_at(state.acks, record.owner, state.acks[record.owner][1:]),
                        receipts=add_id(state.receipts, rid), clients=tuple_at(state.clients, record.owner, None))
        return singleton(after, event(state, "Receipt", record.owner, rid))
    assert name == "Clean" and record.phase == "COOLING" and state.up
    free = state.free + 1 if isinstance(state.free, int) else tuple(sorted(state.free + (record.unit,)))
    after = replace(state, free=free, reservations=tuple(r for r in state.reservations if r.rid != rid))
    return singleton(after, event(state, "Cleaned", record.owner, rid))


def diagnostic_actions(state, generation_limit):
    actions = list(ready(state, generation_limit))
    actions.extend((("Down",) if state.up else ("Up",), ("Tick",)))
    known = tuple(sorted(set(state.queue) | set(record_map(state)) | set(state.receipts)))
    for rid in known:
        actions.append(("Probe", RESOURCE, rid[0], rid))
        actions.append(("Retry", RESOURCE, rid[0], rid))
        if rid in state.applied:
            actions.append(("Apply", rid))
    exemplar = known[0] if known else (0, 0)
    for command in ("Probe", "Retry"):
        actions.extend(((command, "wrong-pool", exemplar[0], exemplar),
                        (command, RESOURCE, (exemplar[0] + 1) % len(state.clients), exemplar),
                        (command, RESOURCE, 0, (0, state.generation[0] + 10))))
    return tuple(dict.fromkeys(actions))


def explore(capacity, concrete, generation_limit=2):
    start = initial(capacity, concrete=concrete)
    todo, seen = deque((start,)), {start}
    edges = 0
    while todo:
        state = todo.popleft()
        invariant(state)
        # Probe/retry/Tick add no successor beyond these core rules.
        actions = ready(state, generation_limit) + (("Down",) if state.up else ("Up",),)
        for action in actions:
            for outcome in transition(state, action):
                edges += 1
                invariant(outcome.state)
                if outcome.state not in seen:
                    seen.add(outcome.state)
                    todo.append(outcome.state)
    return seen, edges


def target_rank(state, rid):
    records = record_map(state)
    if rid in state.queue:
        return state.queue.index(rid) + 1, sum(PHASE_RANK[r.phase] for r in records.values())
    if rid in records:
        return 0, PHASE_RANK[records[rid].phase]
    assert rid in state.receipts
    return 0, 0


def push_outcomes(outcomes):
    law = defaultdict(F)
    for outcome in outcomes:
        law[(abstract(outcome.state), outcome.event)] += outcome.weight
    return dict(law)


def finite_checks():
    reports = []
    for capacity in (1, 2):
        concrete, concrete_edges = explore(capacity, True)
        reference, reference_edges = explore(capacity, False)
        assert {abstract(state) for state in concrete} == reference
        counts = defaultdict(int)
        for state in concrete:
            projected = abstract(state)
            assert ready(state) == ready(projected)
            actions = diagnostic_actions(state, 2)
            targets = tuple(sorted(set(state.queue) | set(record_map(state)) | set(state.receipts)))
            for policy in ("uniform", "first_fit"):
                for action in actions:
                    outcomes = transition(state, action, policy)
                    expected = transition(projected, action)
                    assert sum(o.weight for o in outcomes) == sum(o.weight for o in expected) == 1
                    assert push_outcomes(outcomes) == {(o.state, o.event): o.weight for o in expected}
                    assert len(expected) == 1
                    for outcome in outcomes:
                        assert abstract(outcome.state) == expected[0].state
                        assert outcome.event == expected[0].event
                        invariant(outcome.state)
                        assert ready(outcome.state) == ready(expected[0].state)
                        counts["actual_local_body_squares"] += 1
                    if action[0] in ("Probe", "Retry") and expected[0].event[0] == "Refusal":
                        assert expected[0].state == projected and all(o.state == state for o in outcomes)
                        counts["explicit_refusal_checks"] += 1
                    counts["local_probability_pushforwards"] += 1
            # Rank checks use the reference graph. Uniform allocation outcomes
            # project identically; unit choice cannot repair a failed rank law.
            for rid in targets:
                before = target_rank(projected, rid)
                assert before == target_rank(state, rid)
                transitions = [(action, transition(projected, action)[0].state) for action in actions]
                assert all(target_rank(after, rid) <= before for _, after in transitions)
                counts["rank_nonincrease_checks"] += len(transitions)
                if projected.up and before != (0, 0):
                    strict = [action for action in ready(projected)
                              if target_rank(transition(projected, action)[0].state, rid) < before]
                    assert strict
                    witness = strict[0]
                    # Under permanent availability, rank-stuttering activity
                    # cannot disable this chosen advancing task.
                    for action, after in transitions:
                        if after.up and target_rank(after, rid) == before:
                            assert witness in ready(after)
                            counts["advancing_task_persistence_checks"] += 1
        reports.append({"capacity": capacity, "clients": 2, "diagnostic_generations_per_client": 2,
                        "concrete_reachable_states": len(concrete), "reference_reachable_states": len(reference),
                        "concrete_graph_edges": concrete_edges, "reference_graph_edges": reference_edges,
                        **dict(counts)})
    return reports


RR_CLASSES = (("Submit", 0), ("Submit", 1), ("Reserve", None), ("Reserve", None),
              ("Apply", 0), ("Apply", 1), ("Publish", 0), ("Publish", 1),
              ("Deliver", 0), ("Deliver", 1), ("Submit", 0), ("Submit", 1),
              ("Clean", 0), ("Clean", 1))


def round_robin(state, pointer):
    actions = ready(state)  # No generation bound.
    for offset in range(len(RR_CLASSES)):
        index = (pointer + offset) % len(RR_CLASSES)
        kind, owner = RR_CLASSES[index]
        matches = [action for action in actions if action[0] == kind
                   and (owner is None or (action[1] if kind == "Submit" else action[1][0]) == owner)]
        if matches:
            return min(matches), (index + 1) % len(RR_CLASSES)
    raise AssertionError("Positive-profile round-robin controller unexpectedly blocked.")


@dataclass(frozen=True)
class History:
    states: tuple
    events: tuple = ()
    raw: tuple = ()
    pointers: tuple = (0,)

    def image(self):
        return History(tuple(abstract(state) for state in self.states), self.events,
                       tuple(None for _ in self.raw), self.pointers)

    def truncate(self):
        assert self.events
        return History(self.states[:-1], self.events[:-1], self.raw[:-1], self.pointers[:-1])


def history_step(history, policy, step):
    state, pointer = history.states[-1], history.pointers[-1]
    if step in (7, 8, 9):
        action = {7: ("Down",), 8: ("Tick",), 9: ("Up",)}[step]
        next_pointer = pointer
    else:
        action, next_pointer = round_robin(state, pointer)
    for outcome in transition(state, action, policy):
        yield History(history.states + (outcome.state,), history.events + ((action, outcome.event),),
                      history.raw + (outcome.raw,), history.pointers + (next_pointer,)), outcome.weight


def push_histories(law, transform):
    result = defaultdict(F)
    for history, mass in law.items():
        result[transform(history)] += mass
    return dict(result)


def prefix_replacement_checks():
    reports = []
    horizon = 60
    for capacity in (1, 2):
        reference = {History((initial(capacity, concrete=False),)): F(1)}
        sources = {policy: {History((initial(capacity),)): F(1)}
                   for policy in ("uniform", "first_fit")}
        checks = 0
        peak = {policy: 1 for policy in sources}
        for step in range(horizon):
            old_reference = reference
            next_reference = defaultdict(F)
            for history, mass in reference.items():
                for after, weight in history_step(history, "uniform", step):
                    next_reference[after] += mass * weight
            reference = dict(next_reference)
            assert len(reference) == 1 and sum(reference.values()) == 1
            assert push_histories(reference, lambda h: h.truncate()) == old_reference
            for policy in sources:
                old = sources[policy]
                after_law = defaultdict(F)
                for history, mass in old.items():
                    assert ready(history.states[-1]) == ready(abstract(history.states[-1]))
                    for after, weight in history_step(history, policy, step):
                        invariant(after.states[-1])
                        assert after.image().truncate() == history.image()
                        after_law[after] += mass * weight
                sources[policy] = dict(after_law)
                assert push_histories(sources[policy], lambda h: h.image()) == reference
                assert push_histories(sources[policy], lambda h: h.truncate()) == old
                assert sum(sources[policy].values()) == 1
                peak[policy] = max(peak[policy], len(sources[policy]))
                checks += 1
        last = next(iter(reference)).states[-1]
        receipts = tuple(sum(rid[0] == owner for rid in last.receipts) for owner in range(2))
        assert min(receipts) >= 3 and max(last.generation) > 2
        reports.append({"capacity": capacity, "horizon_service_microsteps": horizon,
                        "receipts_per_recurrent_client": receipts,
                        "next_generations": last.generation, "exact_cost": last.cost,
                        "available_at_boundary": available(last),
                        "native_prefix_law_comparisons": checks,
                        "maximum_retained_raw_histories": peak,
                        "comparison": "Uniform and first-fit physical-unit allocation have the same complete count/phase/queue/receipt/cost history under the declared public controller."})
    return reports


def one(state, action, unit=None):
    choices = transition(state, action)
    if unit is None:
        return choices[0].state
    return next(outcome.state for outcome in choices if outcome.raw == unit)


def invalid(state):
    try:
        invariant(state)
    except AssertionError:
        return True
    return False


def boundaries():
    start = initial(1)
    reserved = one(one(start, ("Submit", 0)), ("Reserve", (0, 0)))
    waiting = one(reserved, ("Submit", 1))
    free_waiting = one(start, ("Submit", 1))
    assert waiting.cost == free_waiting.cost == 0
    assert available(waiting) == 0 and available(free_waiting) == 1
    assert ("Reserve", (1, 0)) not in ready(waiting)
    assert ("Reserve", (1, 0)) in ready(free_waiting)
    applied = one(waiting, ("Apply", (0, 0)))
    assert available(applied) == 0 and applied.applied == ((0, 0),)
    assert not applied.receipts and not any(applied.acks)
    notified = one(applied, ("Publish", (0, 0)))
    cooling = one(notified, ("Deliver", (0, 0)))
    assert cooling.clients[0] is None and available(cooling) == 0
    assert ("Submit", 0) in ready(cooling) and ("Reserve", (1, 0)) not in ready(cooling)
    cleaned = one(cooling, ("Clean", (0, 0)))
    assert available(cleaned) == 1 and cleaned.cost == cooling.cost == 1
    assert cleaned.applied == cleaned.receipts == ((0, 0),)
    replay = transition(cleaned, ("Apply", (0, 0)))[0]
    assert replay.event[0] == "AlreadyApplied" and replay.state == cleaned

    # Freeing the assigned unit before cooling cleanup permits double booking.
    early = replace(applied, free=(0,))
    assert invalid(early)
    collision = one(early, ("Reserve", (1, 0)))
    assert invalid(collision)
    assert [record.unit for record in collision.reservations] == [0, 0]

    # An unchanged E-lookup implementation cannot merely erase E. Here the
    # remaining phase would support reconstruction, but the unchanged lookup
    # returns Refusal instead of AlreadyApplied, and the stored invariant fails.
    forgotten = replace(applied, applied=())
    assert invalid(forgotten)
    good_retry = transition(applied, ("Retry", RESOURCE, 0, (0, 0)))[0]
    bad_retry = transition(forgotten, ("Retry", RESOURCE, 0, (0, 0)))[0]
    assert good_retry.event[0] == "AlreadyApplied" and bad_retry.event[0] == "Refusal"
    reconstructed = set(forgotten.receipts) | {r.rid for r in forgotten.reservations if r.phase != "RESERVED"}
    assert reconstructed == set(applied.applied)

    # Target cannot answer a later unit-specific fault query after erasure.
    two = one(initial(2), ("Submit", 0))
    assigned_zero = one(two, ("Reserve", (0, 0)), 0)
    assigned_one = one(two, ("Reserve", (0, 0)), 1)
    assert abstract(assigned_zero) == abstract(assigned_one)
    fault_zero = record_map(assigned_zero)[(0, 0)].unit == 0
    fault_one = record_map(assigned_one)[(0, 0)].unit == 0
    assert fault_zero and not fault_one

    # Exact lasso witnesses. Both clients wait, so no ignored Submit obligation
    # is accidentally used to call the flickering schedule weakly fair.
    queued = one(one(initial(1), ("Submit", 0)), ("Submit", 1))
    grant = ("Reserve", (0, 0))
    assert ready(queued) == (grant,)
    assert one(queued, ("Tick",)) == queued  # Continuously enabled grant starved.
    down = one(queued, ("Down",))
    assert ready(down) == () and one(down, ("Tick",)) == down
    flicker = [down]
    for action in (("Up",), ("Tick",), ("Down",), ("Tick",)):
        flicker.append(one(flicker[-1], action))
    assert flicker[-1] == down
    menus = [set(ready(state)) for state in flicker[:-1]]
    assert set.intersection(*menus) == set()
    assert set.union(*menus) == {grant}
    zero = one(initial(0), ("Submit", 0))
    assert ("Reserve", (0, 0)) not in ready(zero)
    return {
        "availability_not_cost": {"equal_cost": 0, "free_counts": [1, 0], "same_next_request_enabled": [True, False]},
        "pending_applied_effect": "E contains the request while no acknowledgment is queued or received; its unit is still unavailable.",
        "receipt_not_cleanup": "Delivery makes the client idle and allows recurrence, but the cooling reservation still occupies its unit until Clean.",
        "cleanup_not_refund": "Clean increases availability without reducing exact accumulated work or erasing applied IDs/receipts.",
        "early_free_counterexample": "Two active reservations become assigned concrete unit 0; partition invariant fails.",
        "forget_E_counterexample": "Erasing E without changing its lookup yields Refusal instead of AlreadyApplied and violates the invariant. E is reconstructible from retained phases/receipts here; no necessity of this exact storage field is claimed.",
        "unit_fault_obstruction": {"same_abstract_state": True, "unit_sensitive_answers": [fault_zero, fault_one]},
        "down_forever": "Tick loop with queued clients and up=False; stable availability premise fails.",
        "unfair_tick": "Tick loop while the head grant is continuously enabled; weak fairness fails.",
        "weakly_fair_flicker": "Up,Tick,Down,Tick returns to the same state. Grant is enabled infinitely often but never continuously; weak fairness alone does not force it.",
        "capacity_zero": "A queued request cannot be reserved; the positive theorem needs capacity at least one.",
    }


def main():
    if not __debug__:
        raise RuntimeError("Run without optimization; assertions perform the diagnostics.")
    result = {"status": "PASS", "model": "Named reusable pool, loss-free acknowledgments, durable applied IDs and receipts, FIFO requests, recurrent clients, delayed cleanup.",
              "finite_exhaustive_checks": finite_checks(),
              "recurrent_replacement_prefixes": prefix_replacement_checks(),
              "boundaries": boundaries(),
              "rank": "Queued target: (FIFO position+1, sum active phase ranks); after grant: (0, own phase rank); cleaned target: (0,0). Ranks RESERVED/APPLIED/NOTIFIED/COOLING are 4/3/2/1.",
              "positive_progress_assumptions": "Capacity>=1; eventual permanent up; weak fairness of declared persistent service tasks; no lost acknowledgments or holder waiting for an additional allocation. Fair Submit gives recurrent demand.",
              "scope": "Finite invariant/local-map/rank diagnostics and exact unrestricted-rule prefixes, not an infinite-run proof, an occurrence-runtime implementation bridge, or physical-time/resource validation. The abstract target retains reservation IDs, phases, applied effects and queues, not only a total count."}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
