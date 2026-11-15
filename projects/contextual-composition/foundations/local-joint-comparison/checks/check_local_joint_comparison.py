"""Exact finite diagnostics for local joint native comparison.

These tests corroborate particular instances and separating examples. They do
not prove the general rule-format theorem, physical admission, an unrestricted
categorical completion, or any Byzantine-control mission.
"""

from fractions import Fraction as F
from itertools import permutations, product
import json


def law(rows):
    result = {}
    for outcome, mass in rows:
        mass = F(mass)
        assert mass >= 0
        result[outcome] = result.get(outcome, F(0)) + mass
    return {outcome: mass for outcome, mass in result.items() if mass}


def push(mu, function):
    return law((function(x), p) for x, p in mu.items())


def probability(mu):
    assert sum(mu.values(), F(0)) == 1
    assert all(type(p) is F and p > 0 for p in mu.values())
    return mu


def total_variation(mu, nu):
    return sum((abs(mu.get(x, F(0)) - nu.get(x, F(0)))
                for x in set(mu) | set(nu)), F(0)) / 2


def product_mass(values, weights):
    value = F(1)
    for bit in values:
        value *= weights[bit]
    return value


BIT = (0, 1)
AUX = {0: F(1, 3), 1: F(2, 3)}
FAIR = {0: F(1, 2), 1: F(1, 2)}
COUPLINGS = {
    "diagonal": {(0, 0): F(1, 2), (1, 1): F(1, 2)},
    "antidiagonal": {(0, 1): F(1, 2), (1, 0): F(1, 2)},
    "independent": {pair: F(1, 4) for pair in product(BIT, repeat=2)},
}


def coupling_transport():
    """Two consecutive noninjective native erasures retain each chosen law."""
    report = {}
    raw_source = set(product(product(BIT, repeat=3), repeat=2))
    raw_middle = set(product(product(BIT, repeat=2), repeat=2))
    raw_target = set(product(BIT, repeat=2))
    first = lambda pair: tuple((w[0], w[1]) for w in pair)
    second = lambda pair: tuple(w[0] for w in pair)
    direct = lambda pair: tuple(w[0] for w in pair)
    assert {first(w) for w in raw_source} == raw_middle
    assert {second(w) for w in raw_middle} == raw_target
    assert len(raw_source) > len(raw_middle) > len(raw_target)
    assert all(second(first(w)) == direct(w) for w in raw_source)
    component_source = probability(law(
        ((b, a, z), FAIR[b] * AUX[a] * AUX[z])
        for b, a, z in product(BIT, repeat=3)))
    for name, joint in COUPLINGS.items():
        probability(joint)
        assert push(joint, lambda pair: pair[0]) == FAIR
        assert push(joint, lambda pair: pair[1]) == FAIR
        source = probability(law(
            (((b0, a0, z0), (b1, a1, z1)), p * product_mass((a0, z0, a1, z1), AUX))
            for (b0, b1), p in joint.items()
            for a0, z0, a1, z1 in product(BIT, repeat=4)))
        assert push(source, lambda pair: pair[0]) == component_source
        assert push(source, lambda pair: pair[1]) == component_source
        middle = push(source, first)
        assert push(middle, second) == push(source, direct) == joint
        report[name] = {
            "positive_source_rows": len(source),
            "positive_middle_rows": len(middle),
            "positive_target_rows": len(joint),
            "native_composite_equals_composed_native_maps": True,
        }
    return {
        "couplings": report,
        "raw_carriers": [len(raw_source), len(raw_middle), len(raw_target)],
        "raw_carrier_kept_separate_from_probability_support": True,
    }


def chooser_boundaries():
    diagonal = COUPLINGS["diagonal"]
    antidiagonal = COUPLINGS["antidiagonal"]
    independent = COUPLINGS["independent"]
    # Identity component maps preserve both fair marginals, yet the target's
    # separately chosen independent coupling is not the transported diagonal.
    assert all(push(diagonal, lambda pair, i=i: pair[i]) ==
               push(independent, lambda pair, i=i: pair[i]) for i in range(2))
    assert diagonal != independent
    assert total_variation(diagonal, independent) == F(1, 2)
    # Two source states have one retained image but select different couplings.
    h = lambda hidden: "same-visible-state"
    selected = {0: diagonal, 1: antidiagonal}
    assert h(0) == h(1) and selected[0] != selected[1]
    assert total_variation(selected[0], selected[1]) == 1
    # A common retained choice tag repairs chooser descent; hiding it does not.
    target_with_tag = {(h(s), s): selected[s] for s in BIT}
    assert all(target_with_tag[(h(s), s)] == selected[s] for s in BIT)
    # For a constant choice, descent also holds without adding a tag.
    constant = {s: diagonal for s in BIT}
    assert constant[0] == constant[1]
    return {
        "same_marginals_do_not_preserve_a_separately_chosen_joint_law": True,
        "chosen_target_mismatch_TV": str(F(1, 2)),
        "hidden_choice_fails_descent": True,
        "hidden_choice_TV": "1",
        "retained_choice_tag_or_constant_choice_passes": True,
    }


def raw_coverage_boundaries():
    # Source boundaries distinguish0/1; the target boundary forgets the bit.
    # Each component raw map is identity (hence onto), but compatible tuples
    # change from the diagonal to the complete product.
    source_joint = {(a, b) for a, b in product(BIT, repeat=2) if a == b}
    target_joint = set(product(BIT, repeat=2))
    r0 = r1 = lambda x: x
    image = {(r0(a), r1(b)) for a, b in source_joint}
    assert {r0(x) for x in BIT} == set(BIT)
    assert {r1(x) for x in BIT} == set(BIT)
    assert image < target_joint and target_joint - image == {(0, 1), (1, 0)}
    # The transported law is nevertheless a valid target coupling.
    assert push(COUPLINGS["diagonal"], lambda w: w) == COUPLINGS["diagonal"]

    # Positive rooted chain0--1--2. Root and leaf carry one boundary bit;
    # the middle carries two. Erasure keeps the actual target outcome bit.
    root = set(product(BIT, repeat=2))       # (value, boundary01)
    middle = set(product(BIT, repeat=3))    # (value, boundary01, boundary12)
    leaf = set(product(BIT, repeat=2))      # (value, boundary12)
    source_chain = {
        (a, b, c) for a, b, c in product(root, middle, leaf)
        if a[1] == b[1] and b[2] == c[1]
    }
    target_chain = set(product(BIT, repeat=3))
    projection = lambda abc: (abc[0][0], abc[1][0], abc[2][0])
    assert {projection(w) for w in source_chain} == target_chain
    relative_checks = 0
    for value, parent_boundary in product(BIT, repeat=2):
        assert any(w[0] == value and w[1] == parent_boundary for w in middle)
        assert any(w[0] == value and w[1] == parent_boundary for w in leaf)
        relative_checks += 2
    for a, b, c in target_chain:
        # Root choice fixes the first boundary; child choices propagate it.
        lifted = ((a, 0), (b, 0, 1), (c, 1))
        assert lifted in source_chain and projection(lifted) == (a, b, c)
    # Correlated target parity law, lifted with two independent boundary bits.
    target_law = probability({w: F(1, 4) for w in target_chain if sum(w) % 2 == 0})
    source_law = probability(law(
        (((a, u), (b, u, v), (c, v)), p / 4)
        for (a, b, c), p in target_law.items()
        for u, v in product(BIT, repeat=2)))
    assert push(source_law, projection) == target_law
    assert push(source_law, lambda w: w[0]) == {w: F(1, 4) for w in root}
    assert push(source_law, lambda w: w[1]) == {w: F(1, 8) for w in middle}
    assert push(source_law, lambda w: w[2]) == {w: F(1, 4) for w in leaf}
    return {
        "component_surjectivity_does_not_imply_joint_surjectivity": True,
        "unlifted_target_pairs": sorted(target_joint - image),
        "positive_chain_source_rows": len(source_chain),
        "positive_chain_target_rows": len(target_chain),
        "local_relative_lift_checks": relative_checks,
        "correlated_law_transport_and_all_raw_lifts_pass": True,
    }


def enabled(state):
    _, _, pcs = state
    return {(kind, job) for job, pc in enumerate(pcs)
            for kind in (("read",) if pc == 0 else ("write",) if pc == 1 else ())}


def target_increment_step(state, operation):
    assert operation in enabled(state)
    world, cache, pcs = state
    cache = list(cache)
    pcs = list(pcs)
    kind, job = operation
    if kind == "read":
        cache[job] = world
        pcs[job] = 1
        event = ("read", job, world)
    else:
        world = cache[job] + 1
        pcs[job] = 2
        event = ("write", job, world)
    return (world, tuple(cache), tuple(pcs)), event


def source_enabled(state):
    """Separate concrete menu computation; cache validity is checked here."""
    (world, caches, counters), _history = state
    result = set()
    for job in range(2):
        if counters[job] == 0:
            result.add(("read", job))
        elif counters[job] == 1 and type(caches[job]) is int:
            result.add(("write", job))
    return result


def source_increment_step(state, operation, auxiliary):
    assert operation in source_enabled(state)
    (world, caches, counters), history = state
    caches = list(caches)
    counters = list(counters)
    kind, job = operation
    if kind == "read":
        caches[job] = world
        counters[job] += 1
        event = (kind, job, caches[job])
    else:
        world = caches[job] + 1
        counters[job] += 1
        event = (kind, job, world)
    return ((world, tuple(caches), tuple(counters)), history + (auxiliary,)), event


def interfering_schedules():
    operations = (("read", 0), ("write", 0), ("read", 1), ("write", 1))
    schedules = [order for order in permutations(operations)
                 if order.index(("read", 0)) < order.index(("write", 0))
                 and order.index(("read", 1)) < order.index(("write", 1))]
    assert len(schedules) == 6
    initial = (0, (None, None), (0, 0))
    records = []
    prefix_comparisons = 0
    for order in schedules:
        concrete = {((initial, ()), ()): F(1)}
        abstract = {(initial, ()): F(1)}
        for operation in order:
            next_concrete = []
            for (state, trace), p in concrete.items():
                assert operation in source_enabled(state)
                for auxiliary, weight in AUX.items():
                    after, event = source_increment_step(state, operation, auxiliary)
                    next_concrete.append(((after, trace + (event,)), p * weight))
            concrete = probability(law(next_concrete))
            next_abstract = []
            for (state, trace), p in abstract.items():
                after, event = target_increment_step(state, operation)
                next_abstract.append(((after, trace + (event,)), p))
            abstract = probability(law(next_abstract))
            assert push(concrete, lambda z: (z[0][0], z[1])) == abstract
            target_ready = set().union(*(enabled(z[0]) for z in abstract))
            assert all(source_enabled(z[0]) == target_ready for z in concrete)
            prefix_comparisons += 1
        (final_state, trace), = abstract.keys()
        assert len(concrete) == 16 and len(abstract) == 1
        records.append({
            "schedule": [kind + str(job) for kind, job in order],
            "final_world": final_state[0],
            "trace": trace,
        })
    assert sum(row["final_world"] == 1 for row in records) == 4
    assert sum(row["final_world"] == 2 for row in records) == 2
    assert len({tuple(map(tuple, row["trace"])) for row in records}) == 6
    return {
        "legal_schedules": records,
        "exact_prefix_pushforwards": prefix_comparisons,
        "lost_update_schedules": 4,
        "serial_result_schedules": 2,
        "chronological_traces_retained": True,
        "noninjective_private_history_erasure": True,
        "independently_computed_menus_match_on_generated_prefixes": True,
    }


def target_kernel(state, command):
    assert state in BIT and command in BIT
    p = F(1, 3) if state == command else F(2, 3)
    return {0: 1 - p, 1: p}


def source_kernel(state, command):
    visible, _hidden = state
    return probability(law(
        ((bit, auxiliary), p * AUX[auxiliary])
        for bit, p in target_kernel(visible, command).items()
        for auxiliary in BIT))


def target_step(state, command, raw):
    return state ^ command ^ raw


def source_step(state, command, raw):
    bit, auxiliary = raw
    return (target_step(state[0], command, bit), auxiliary)


def conditional_bind_and_feedback():
    primitive_cases = 0
    for state, hidden, command in product(BIT, repeat=3):
        concrete = (state, hidden)
        assert push(source_kernel(concrete, command), lambda w: w[0]) == target_kernel(state, command)
        for raw in source_kernel(concrete, command):
            assert source_step(concrete, command, raw)[0] == target_step(state, command, raw[0])
        primitive_cases += 1

    # The second command is selected from the actual intermediate result.
    source_pairs = []
    target_pairs = []
    for first, p in source_kernel((0, 1), 0).items():
        middle = source_step((0, 1), 0, first)
        command = middle[0]
        for second, q in source_kernel(middle, command).items():
            source_pairs.append(((first, second), p * q))
    for first, p in target_kernel(0, 0).items():
        middle = target_step(0, 0, first)
        for second, q in target_kernel(middle, middle).items():
            target_pairs.append(((first, second), p * q))
    assert push(probability(law(source_pairs)), lambda ws: tuple(w[0] for w in ws)) == probability(law(target_pairs))

    # Strict delay: initial command1; next command is the preceding public
    # output. The source's hidden auxiliary state never enters the controller.
    source_prefixes = {((0, 1), (), (), 1): F(1)}
    target_prefixes = {(0, (), (), 1): F(1)}
    horizons = []
    effect_truncation_checks = 0

    def source_prefix_from_raw(raws):
        state, trace, command = (0, 1), (), 1
        for raw in raws:
            after = source_step(state, command, raw)
            trace += ((command, raw[0], after[0]),)
            state, command = after, after[0]
        return state, raws, trace, command

    def target_prefix_from_raw(raws):
        state, trace, command = 0, (), 1
        for raw in raws:
            after = target_step(state, command, raw)
            trace += ((command, raw, after),)
            state, command = after, after
        return state, raws, trace, command

    for depth in range(6):
        projection = lambda z: (z[0][0], tuple(w[0] for w in z[1]), z[2], z[3])
        assert push(source_prefixes, projection) == target_prefixes
        horizons.append({"depth": depth, "source_rows": len(source_prefixes), "target_rows": len(target_prefixes)})
        if depth == 5:
            break
        source_next = []
        target_next = []
        for (state, raws, trace, command), p in source_prefixes.items():
            for raw, q in source_kernel(state, command).items():
                after = source_step(state, command, raw)
                event = (command, raw[0], after[0])
                source_next.append(((after, raws + (raw,), trace + (event,), after[0]), p * q))
                # Raw-map truncation is the same operation at every horizon.
                assert tuple(w[0] for w in (raws + (raw,)))[:-1] == tuple(w[0] for w in raws)
        for (state, raws, trace, command), p in target_prefixes.items():
            for raw, q in target_kernel(state, command).items():
                after = target_step(state, command, raw)
                event = (command, raw, after)
                target_next.append(((after, raws + (raw,), trace + (event,), after), p * q))
        next_source_law = probability(law(source_next))
        next_target_law = probability(law(target_next))
        assert push(next_source_law, lambda z: source_prefix_from_raw(z[1][:-1])) == source_prefixes
        assert push(next_target_law, lambda z: target_prefix_from_raw(z[1][:-1])) == target_prefixes
        effect_truncation_checks += 2
        source_prefixes = next_source_law
        target_prefixes = next_target_law
    return {
        "all_state_command_primitive_cases": primitive_cases,
        "dependent_two_step_bind_exact": True,
        "guarded_feedback_horizons": horizons,
        "native_maps_commute_with_raw_prefix_truncation": True,
        "exact_effect_prefix_truncation_checks": effect_truncation_checks,
        "scope": "Six finite horizons corroborate the example; the general prefix/feedback theorem needs its written induction.",
    }


def admission_is_not_endpoint_equality():
    stock = 10
    requests = (7, 7)
    separately_reported = tuple(stock - request for request in requests)
    assert separately_reported == (3, 3)
    assert sum(requests) > stock
    return {
        "equal_separate_poststocks": separately_reported,
        "distinct_requested_debits": requests,
        "joint_budget_guard_rejects": True,
        "scope": "Separating example for a declared additive charge law; not a physical Byzantine execution.",
    }


def main():
    if not __debug__:
        raise RuntimeError("Run without Python optimization; assertions are the diagnostics.")
    result = {
        "status": "PASS",
        "coupling_transport": coupling_transport(),
        "chooser_boundaries": chooser_boundaries(),
        "raw_coverage": raw_coverage_boundaries(),
        "interfering_microsteps": interfering_schedules(),
        "bind_and_feedback": conditional_bind_and_feedback(),
        "physical_admission_boundary": admission_is_not_endpoint_equality(),
        "scope": "Exact Fraction diagnostics for finite instances and counterexamples; no general proof, physical admission, or full categorical feedback/concurrency theorem.",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
