"""Exhaustive finite checks for the discrete fragment. Python is evidence, not a proof kernel.
All functions use standard-library Python 3.12. No network or third-party dependencies.
"""
from itertools import product, combinations
from collections import defaultdict
import argparse
import json
from pathlib import Path
from fractions import Fraction

STATES = tuple(range(2, 9))
CONTROLS = (0, 1, 2)
BYPASS = (-1, 0, 1)
IDS = (0, 1, 2)
FAULTS = (None, 0, 1, 2)


def median(values):
    return sorted(values)[1]


def envelope(m):
    return tuple(x for x in STATES if abs(x - m) <= 1)


def safe_actions(m):
    e = envelope(m)
    assert e, ("inconsistent evidence", m)
    return frozenset(u for u in CONTROLS
                     if all(2 <= x + u - 1 + b <= 8 for x in e for b in BYPASS))


def common_witness(x):
    return min(2, max(0, 6 - x))


def subsets(values):
    return tuple(frozenset(c) for r in range(len(values) + 1) for c in combinations(values, r))


def accepted(endorsements):
    return frozenset(u for u in CONTROLS if sum(u in e for e in endorsements.values()) >= 2)


def physical():
    configurations = transitions = 0
    edges = defaultdict(set)
    fault_regions = {}
    distinct_evidence = False
    for bs, bc in product(FAULTS, repeat=2):
        # The SAME pair (bs,bc) persists across all future transitions.
        # This enumerates the explicitly declared joint family, not separate proofs.
        good_s = tuple(i for i in IDS if i != bs)
        good_c = tuple(i for i in IDS if i != bc)
        visited = set()
        for x in STATES:
            for ys in product(range(x - 1, x + 2), repeat=len(good_s)):
                readings = dict(zip(good_s, ys))
                if bs is None:
                    choices = (median(ys),)
                    assignments = [tuple(choices[0] for _ in good_c)]
                else:
                    # With two fixed honest readings, the attack's exact median image
                    # is every integer between them. Any such m is attained by report m.
                    choices = tuple(range(min(ys), max(ys) + 1))
                    assignments = product(choices, repeat=len(good_c))
                    for malicious in range(-2, 13):
                        assert min(ys) <= median((*ys, malicious)) <= max(ys)
                    for m in choices:
                        assert median((*ys, m)) == m
                for ms in assignments:
                    mids = dict(zip(good_c, ms))
                    honest = {i: safe_actions(mids[i]) for i in good_c}
                    for i in good_c:
                        assert x in envelope(mids[i])
                        assert common_witness(x) in honest[i]
                    if len(set(ms)) > 1:
                        distinct_evidence = True
                    malicious_options = subsets(CONTROLS) if bc is not None else (frozenset(),)
                    for malicious in malicious_options:
                        endorses = dict(honest)
                        if bc is not None:
                            endorses[bc] = malicious
                        certs = accepted(endorses)
                        assert certs, ("availability", x, bs, bc, readings, mids)
                        # Gate waits for the fixed deadline, then chooses min(certs).
                        # Safety is checked for EVERY certified choice, a stronger claim.
                        selected = min(certs)
                        assert selected in certs
                        configurations += 1
                        visited.add(x)
                        for u, b in product(certs, BYPASS):
                            y = x + u - 1 + b
                            assert y in STATES, (x, u, b, endorses)
                            transitions += 1
                            edges[(bs, bc, x)].add(y)
        assert visited == set(STATES)
        fault_regions[str((bs, bc))] = sorted(visited)
    # Finite invariant replay: every allowed edge remains in the same safe fault fiber.
    for (bs, bc, x), targets in edges.items():
        assert targets
        assert all((bs, bc, y) in edges for y in targets)
    assert distinct_evidence
    return dict(configurations=configurations, certified_transitions=transitions,
                fault_fibers=len(fault_regions), winning_region=list(STATES),
                successor_fibers=len(edges), service_units_per_epoch=1,
                infinite_horizon_basis="Control.lean loop_invariant plus recurring construction",
                attack_quotient="all attainable recipient medians; all Byzantine endorsement subsets")


def broadcast():
    # Three identities: leader0, followers1/2. Two round deadlines.
    values = (0, 1)
    all_sets = subsets(values)
    cases = 0
    late_rejections = 0
    def choose(s):
        return next(iter(s)) if len(s) == 1 else 0
    for bad in FAULTS:
        for leader_input in values:
            if bad == 0:
                # Every subset of valid raw leader values to each follower in round1.
                for r1a, r1b, late_a, late_b in product(all_sets, repeat=4):
                    r1 = {1: r1a, 2: r1b}
                    # Correct followers sign/forward their first-round sets.
                    echo = {1: r1[2], 2: r1[1]}
                    final = {i: set(r1[i] | echo[i]) for i in (1, 2)}
                    # No faulty follower exists: any admissible echo is an honest echo.
                    # Raw leader messages in round2 lack the required follower signature.
                    late_rejections += len(late_a) + len(late_b)
                    out = {i: choose(final[i]) for i in (1, 2)}
                    assert out[1] == out[2]
                    cases += 1
            else:
                # A correct leader signs only its actual bit. A faulty follower may
                # omit/echo/replay it, but cannot forge a signature on the other bit.
                options = (frozenset(), frozenset((leader_input,)))
                for faulty_echo in options:
                    out = {0: leader_input}
                    for i in (1, 2):
                        if i != bad:
                            incoming = {leader_input}
                            incoming.update(faulty_echo)
                            out[i] = choose(incoming)
                    assert set(out.values()) == {leader_input}
                    cases += 1
    # Concrete timing failure if round2 raw proposals are admitted.
    assert choose({1}) != choose(set())
    return dict(enumeration_cases=cases, late_raw_values_rejected=late_rejections,
                identities=3, max_faults=1, rounds=2,
                late_injection_counterexample={"round1": [[], []],
                                               "round2_raw": [[1], []],
                                               "bad_outputs_if_accepted": [1, 0]},
                refinement="two-round signed broadcast specialization; no external-effect validity")


def structural():
    results = []
    # Exhaust every nonempty adversary family on universes of size 1..3.
    # Existence checked by the maximal safe family: if it lacks availability,
    # no subfamily can restore availability. This is independent of complement construction.
    for n in range(1, 4):
        universe = frozenset(range(n))
        all_q = subsets(tuple(universe))
        for family in subsets(all_q):
            if not family:
                continue
            q2 = all(a | b != universe for a, b in product(family, repeat=2))
            q3 = all(a | b | c != universe for a, b, c in product(family, repeat=3))
            hit = [q for q in all_q if all(not q <= b for b in family)]
            hit_available = all(any(q.isdisjoint(b) for q in hit) for b in family)
            assert q2 == hit_available
            # Q3 sufficiency by complement family; necessity is separately in Lean.
            complements = [universe - b for b in family]
            consistent = all(not (q & r) <= b for q, r, b in product(complements, complements, family))
            assert consistent == q3
            results.append((n, q2, q3))
    # Physical role universe size3: Q2 true, Q3 false.
    family = [frozenset((i,)) for i in IDS]
    assert all(a | b != frozenset(IDS) for a, b in product(family, repeat=2))
    assert frozenset.union(*family) == frozenset(IDS)
    return dict(families_checked=len(results), universe_sizes=[1, 2, 3],
                role_three_one_fault={"Q2": True, "Q3": False})


def epistemic():
    # Source world = (fixed physical truth, two delivery events).
    # An event mask specifies which of A,B receive the same authenticated claim.
    # Sender may be Byzantine; no truth precondition is imposed.
    worlds = tuple(product((False, True), range(4), range(4)))
    def observations(w, actor):
        return tuple(bool(mask & (1 << actor)) for mask in w[1:])
    def atoms(w):
        return (w[0], any(observations(w, 0)), any(observations(w, 1)))
    def product_world(w):
        # Iterated ontic DEL product with receipt postconditions.
        return ((w[0], w[1]), w[2])
    def product_observations(p, actor):
        return (bool(p[0][1] & (1 << actor)), bool(p[1] & (1 << actor)))
    def product_atoms(p):
        return (p[0][0], bool((p[0][1] | p[1]) & 1), bool((p[0][1] | p[1]) & 2))
    pairs = 0
    for w in worlds:
        assert atoms(w) == product_atoms(product_world(w))
        for v, actor in product(worlds, (0, 1)):
            assert (observations(w, actor) == observations(v, actor)) == (
                product_observations(product_world(w), actor) == product_observations(product_world(v), actor))
            pairs += 1
    def knows(w, actor, fact, model=worlds):
        return all(fact(v) for v in model if observations(w, actor) == observations(v, actor))
    actual = (True, 1, 0)
    assert knows(actual, 0, lambda w: atoms(w)[1])
    assert not knows(actual, 0, lambda w: w[0])
    assert not knows(actual, 1, lambda w: atoms(w)[1])
    false_actual = (False, 1, 0)
    assert false_actual in worlds
    announced = tuple(w for w in worlds if w[0])
    assert knows(actual, 0, lambda w: w[0], announced)
    assert false_actual not in announced
    return dict(worlds=len(worlds), accessibility_comparisons=pairs,
                atom_and_relation_isomorphism=True,
                consequences="all Boolean/nested-knowledge queries by structural induction",
                not_preserved="temporal, strategic, deadline claims without further semantics",
                false_announcement_and_selective_delivery_witnesses=True)



def certificate_epistemic():
    # h is a historical signing fact. c=>h is the supplied signature-soundness
    # contract; physical truth p is independent. This model does NOT prove c=>h.
    initial = tuple(w for w in product((False, True), repeat=3) if not w[2] or w[1])
    direct = [(w, ()) for w in initial]
    # Separate product records: original world, event path, atom valuation, observations.
    prod = [(w, (), (w[0], w[1], w[2], False), ((), ())) for w in initial]
    counts = []
    comparisons = 0
    for stage in range(3):
        direct = [(w, seq+(event,)) for w, seq in direct for event in (0, 1)
                  if not event or w[2]]
        updated = []
        for w, seq, val, obs in prod:
            for event in (0, 1):
                if event and not val[2]:
                    continue
                new_val = (*val[:3], val[3] or bool(event))
                new_obs = (obs[0]+(event,), obs[1]+(0,))
                updated.append((w, seq+(event,), new_val, new_obs))
        prod = updated
        lookup = {(w, seq): (val, obs) for w, seq, val, obs in prod}
        assert len(lookup) == len(direct) == len(prod)
        for w, seq in direct:
            val, obs = lookup[(w, seq)]
            assert val == (*w, bool(any(seq)))
            assert obs == (seq, (0,)*len(seq))
            for v, other in direct:
                ov, oo = lookup[(v, other)]
                for actor in (0, 1):
                    direct_equal = seq == other if actor == 0 else len(seq) == len(other)
                    assert direct_equal == (obs[actor] == oo[actor])
                    comparisons += 1
        counts.append(len(direct))
    actual = ((False, True, True), (1, 0, 0))
    def knows(actor, atom):
        _, actual_obs = lookup[actual]
        return all(val[atom] for val, obs in lookup.values() if obs[actor] == actual_obs[actor])
    assert knows(0, 3) and knows(0, 2) and knows(0, 1) and not knows(0, 0)
    assert not knows(1, 3) and not knows(1, 2) and not knows(1, 1)
    return dict(initial_worlds=len(initial), worlds_by_stage=counts,
                accessibility_comparisons=comparisons,
                knows_historical_fact_not_physical_truth=True,
                outsider_does_not_learn_possession=True,
                trust_boundary="c implies h assumed from signature provenance, not proved here")


def failures():
    # Same control objective and plant; deterministic singleton endorsements can stall.
    assert safe_actions(4) == {1, 2}
    assert safe_actions(6) == {0, 1}
    singleton = {0: {min(safe_actions(4))}, 1: {min(safe_actions(6))}, 2: set()}
    permissive = {0: safe_actions(4), 1: safe_actions(6), 2: set()}
    assert not accepted(singleton)
    assert accepted(permissive) == {1}
    # At x5, honest sensor readings4,6 and Byzantine report4/6 realize those medians.
    assert median((4, 6, 4)) == 4 and median((4, 6, 6)) == 6
    # Every no-sensing action fails at an endpoint, a policy-independent first-step obstruction.
    for u in CONTROLS:
        assert not (2 <= 2 + u - 2 <= 8 and 2 <= 8 + u <= 8)
    # Reduced capacity, excessive hostile bypass, duplicate and stale execution.
    assert all(2 + u - 2 < 2 for u in (0, 1))
    assert all(2 + u - 3 < 2 for u in CONTROLS)
    assert 2 in safe_actions(4)
    assert {1, 2} <= safe_actions(5)
    assert 6 + 1 + 2 - 1 + 1 == 9
    assert 8 + 2 - 1 + 1 == 10  # agreed command need not have safe physical effect
    duplicate = 5 + 2 * 2 - 1 + 1
    assert duplicate == 9
    stale_trace = [5, 7, 9]  # m4,u2 used fresh once and stale once; b=1.
    assert all(stale_trace[t+1] == stale_trace[t] + 2 - 1 + 1 for t in (0, 1))
    # Permanent shutdown is not a winning fallback.
    shutdown = [2, 1]
    assert shutdown[-1] not in STATES
    # Evidence bound violated: two bad sensors report5 at x2 -> m5 endorses0.
    assert median((2, 5, 5)) == 5 and 0 in safe_actions(5)
    assert 2 + 0 - 1 - 1 == 0
    # Two faulty authorizers can provide the bad certificate without an honest endorsement.
    assert 0 in accepted({0: {0}, 1: {0}, 2: {2}})
    # Correct delivery is a safety premise, not merely a service premise.
    assert median((7, 0, 2)) == 2 and safe_actions(2) == {2}
    assert 8 + 2 - 1 + 1 == 10
    # With honest error2 and appropriately expanded envelopes, sound local actions
    # may have no intersection. x5, honest readings3/7, equivocation3 vs7.
    def expanded(m, error):
        return frozenset(u for u in CONTROLS if all(
            2 <= z + u - 1 + b <= 8
            for z in STATES if abs(z - m) <= error for b in BYPASS))
    assert expanded(3, 2) == {2} and expanded(7, 2) == {0}
    # Real-valued variant: exact rational arithmetic, endpoint checks are sufficient
    # because affine effects attain extrema at interval endpoints.
    def real_actions(m):
        lo, hi = max(Fraction(2), m-1), min(Fraction(8), m+1)
        return frozenset(u for u in CONTROLS if 2 <= lo+u-2 and hi+u <= 8)
    real_left, real_right = real_actions(Fraction(7, 2)), real_actions(Fraction(11, 2))
    assert real_left == {2} and real_right == {0, 1}
    assert not real_left & real_right
    # Fractional bypass alone reaches x4.5; the subsequent availability witness
    # also extends readings/envelopes to real intervals, retaining integer controls.
    assert Fraction(4) + 1 - 1 + Fraction(1, 2) == Fraction(9, 2)
    assert 1 in safe_actions(4)
    # Exact state and attribution remain unidentified even while action1 is safe.
    indistinguishable_states = [4, 5, 6]  # every honest sensor may report5 in each.
    assert all(abs(x - 5) <= 1 for x in indistinguishable_states)
    assert safe_actions(5) == {0, 1, 2}
    # Exhaust all locally certified median-only singleton tables (12 choices each).
    medians = tuple(range(1, 10))
    tables = [dict(zip(medians, row)) for row in product(*(sorted(safe_actions(m)) for m in medians))]
    tested = 0
    for profile in product(tables, repeat=3):
        compatible = all(profile[i][m] == profile[j][n]
                         for i, j in combinations(IDS, 2) for x in STATES
                         for m in range(x-1, x+2) for n in range(x-1, x+2))
        assert not compatible
        tested += 1
    return dict(singleton_profiles_rejected=tested, singleton_table_count=len(tables),
                singleton_deadlock={"x": 5, "honest_readings": [4, 6],
                                   "medians": [4, 6], "singleton_votes": [1, 0],
                                   "permissive_common": [1]},
                no_sensing_endpoint_obstruction=True,
                reduced_capacity=True, bypass_minus_two=True,
                duplicate_execution_endpoint=duplicate, stale_trace=stale_trace,
                shutdown_trace=shutdown, two_bad_sensors_endpoint=0,
                two_bad_authorizers_can_certify_zero_at_x2=True,
                missing_correct_sensor_endpoint=10, increased_error_empty_intersection=True,
                continuous_transfer_failure={"x": "9/2", "medians": ["7/2", "11/2"],
                                             "local_controls": [[2], [0, 1]]},
                indistinguishable_states=indistinguishable_states,
                institutional_collapse={"normative_authorized": False,
                                        "credential_accepted": True,
                                        "unprotected_effect": True})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {"physical": physical(), "digital": broadcast(), "structural": structural(),
              "epistemic": epistemic(), "certificate_epistemic": certificate_epistemic(),
              "counterexamples": failures()}
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
