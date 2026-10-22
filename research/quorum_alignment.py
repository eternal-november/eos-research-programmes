"""Finite replay of operational Q3 signing alignment; no consensus claim."""
from itertools import combinations
import json

ACTORS = tuple(range(4))
FAULTS = (None,) + ACTORS
REQUESTS = (None,) + tuple((i, v) for i in ACTORS for v in (0, 1))


def local_action(own_signatures, value):
    return ("sign", value) if not own_signatures or own_signatures == (value,) else ("reject",)


def own_view(facts, actor):
    return tuple(v for v in (0, 1) if facts & (1 << (2*actor+v)))


def step(facts, bad, request):
    if request is None:
        return facts
    actor, value = request
    # Fault mask selects the component implementation; local_action does not see it.
    if actor == bad or local_action(own_view(facts, actor), value)[0] == "sign":
        return facts | (1 << (2*actor+value))
    return facts


def certificate(facts, value):
    return any(all(facts & (1 << (2*i+value)) for i in support)
               for support in combinations(ACTORS, 3))


def run_checks():
    total_states = edges = available = receipts = 0
    for bad in FAULTS:
        seen, todo = {0}, [0]
        while todo:
            facts = todo.pop()
            total_states += 1
            assert not (certificate(facts, 0) and certificate(facts, 1))
            sub = facts
            accepted_values = set()
            while True:
                assert sub & ~facts == 0  # Receipt-to-issued authenticity refinement.
                for value in (0, 1):
                    if certificate(sub, value):
                        assert certificate(facts, value)
                        accepted_values.add(value)
                receipts += 1
                if sub == 0:
                    break
                sub = (sub - 1) & facts
            assert len(accepted_values) <= 1  # Different receivers cannot accept conflicts.
            for actor in ACTORS:
                if actor != bad:
                    assert len(own_view(facts, actor)) <= 1
            for request in REQUESTS:
                target = step(facts, bad, request)
                # An independently stated fact-update relation supplies the replay.
                if request is None:
                    expected = facts
                else:
                    i, v = request
                    forbidden_other = facts & (1 << (2*i+(1-v)))
                    expected = facts if i != bad and forbidden_other else facts | (1 << (2*i+v))
                assert target == expected and (facts & target) == facts
                edges += 1
                if target not in seen:
                    seen.add(target)
                    todo.append(target)
        expected_count = 3**4 if bad is None else 4 * 3**3
        assert len(seen) == expected_count
        for value in (0, 1):
            facts = 0
            for actor in ACTORS:
                if actor != bad:
                    facts = step(facts, bad, (actor, value))
            assert certificate(facts, value)
            available += 1
    # Dropping the own-history guard allows both certificates even with no faults.
    unguarded = (1 << 8) - 1
    assert certificate(unguarded, 0) and certificate(unguarded, 1)
    # Q2 with 2-of-3 supports does not provide ordinary conflict exclusion:
    # honest0 signs0, honest1 signs1, Byzantine2 signsboth.
    split = (1 << 0) | (1 << 3) | (1 << 4) | (1 << 5)
    assert sum(bool(split & (1 << (2*i))) for i in range(3)) == 2
    assert sum(bool(split & (1 << (2*i+1))) for i in range(3)) == 2
    stalled = 0
    stalled_requests = ((0, 0), (1, 1), (2, 1), (0, 1), (1, 0), (2, 0))
    for request in stalled_requests:
        stalled = step(stalled, 3, request)
        assert not certificate(stalled, 0) and not certificate(stalled, 1)
    assert all(step(stalled, 3, req) == stalled for req in ((0, 1), (1, 0), (2, 0), None))
    return {"q3_signing_liveness_counterexample": {"faulty": 3,
                "requests": stalled_requests, "facts": stalled, "no_certificate": True},
            "reachable_fact_states": total_states, "scheduled_request_edges": edges,
            "authentic_receipt_sets": receipts,
            "honest_only_available_publications": available,
            "rejections_are_nonblocking": True,
            "unguarded_conflicting_certificates": True,
            "q2_does_not_replace_q3_for_independent_signing": True,
            "scope": "4 identities, at most 1 fixed fault, 3-share supports, binary values; signing safety only"}


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2, sort_keys=True))
