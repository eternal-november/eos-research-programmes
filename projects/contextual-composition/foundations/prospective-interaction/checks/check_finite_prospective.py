#!/usr/bin/env python3
"""Exact finite diagnostics for Prospective Interaction.

Run with Python 3; only the standard library is used.  The default output is
results.json beside this script.  These are finite arithmetic diagnostics,
not a proof-assistant certificate or a verification of the general native lift.

The policy enumeration evaluates complete raw paths directly.  The Bellman
calculation is a separate backward recursion on the same declared arena.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys
from typing import Dict, Iterable, Mapping, Tuple


History = Tuple[str, ...]


@dataclass(frozen=True)
class Outcome:
    witness: str
    probability: F
    reward: F
    child: History


@dataclass(frozen=True)
class Decision:
    actions: Tuple[str, ...]
    rows: Mapping[str, Tuple[Outcome, ...]]


def hname(h: History) -> str:
    return "root" if not h else "/".join(h)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def make_arena():
    """Three decisions per path, 13 retained decision histories.

    A emits a fair bit. B emits a raw bit with law (1,0), retains both
    witnesses, and pays 1/2 immediately. At each ensuing history, preparation
    costs 1/2 and increases the later work reward from 1 to 2. Raw bit 1
    adds 1/4 to a work reward, including on the zero B/1 branch.
    """
    decisions: Dict[History, Decision] = {}
    terminal: Dict[History, F] = {}
    root_rows = {}
    for a, law, reward in (
        ("A", (F(1, 2), F(1, 2)), F(0)),
        ("B", (F(1), F(0)), F(1, 2)),
    ):
        root_rows[a] = tuple(
            Outcome(str(w), law[w], reward, (a, str(w))) for w in (0, 1)
        )
        for w in (0, 1):
            h = (a, str(w))
            middle_rows = {}
            for b in ("prepare", "skip"):
                child = h + (b, "unit")
                middle_rows[b] = (
                    Outcome("unit", F(1), -F(1, 2) if b == "prepare" else F(0), child),
                )
                final_rows = {}
                for c in ("work", "rest"):
                    leaf = child + (c, "unit")
                    reward2 = (
                        F(2 if b == "prepare" else 1) + (F(1, 4) if w else F(0))
                        if c == "work"
                        else F(0)
                    )
                    final_rows[c] = (Outcome("unit", F(1), reward2, leaf),)
                    terminal[leaf] = F(0)
                decisions[child] = Decision(("work", "rest"), final_rows)
            decisions[h] = Decision(("prepare", "skip"), middle_rows)
    decisions[()] = Decision(("A", "B"), root_rows)
    order = tuple(sorted(decisions, key=lambda h: (len(h), h)))
    assert len(order) == 13
    assert len(terminal) == 16
    for node in decisions.values():
        for a in node.actions:
            row = node.rows[a]
            assert sum((e.probability for e in row), F(0)) == 1
            assert len({e.witness for e in row}) == len(row)
            assert all(e.probability >= 0 for e in row)
            assert all(e.child in decisions or e.child in terminal for e in row)
    return decisions, terminal, order


def backward(decisions, terminal, order):
    values = dict(terminal)
    action_values = {}
    for h in reversed(order):
        node = decisions[h]
        qs = {
            a: sum(
                (e.probability * (e.reward + values[e.child]) for e in node.rows[a]),
                F(0),
            )
            for a in node.actions
        }
        action_values[h] = qs
        values[h] = max(qs.values())
    return values, action_values


def direct_path_value(decisions, terminal, policy):
    """Enumerate selected raw paths, retaining zero-weight raw paths.

    No backward values or local optimum are used in this calculation.
    """
    total = F(0)
    occupancy = {h: F(0) for h in decisions}
    paths = []
    stack = [((), F(1), F(0))]
    while stack:
        h, mass, accumulated_reward = stack.pop()
        if h in terminal:
            payoff = accumulated_reward + terminal[h]
            total += mass * payoff
            paths.append((h, mass, payoff))
            continue
        occupancy[h] += mass
        for e in decisions[h].rows[policy[h]]:
            stack.append(
                (e.child, mass * e.probability, accumulated_reward + e.reward)
            )
    assert sum((mass for _, mass, _ in paths), F(0)) == 1
    return total, occupancy, paths


def arena_diagnostic():
    decisions, terminal, order = make_arena()
    values, qs = backward(decisions, terminal, order)
    greedy = {
        h: tuple(a for a in decisions[h].actions if qs[h][a] == values[h])
        for h in order
    }
    assert all(len(aa) == 1 for aa in greedy.values())
    all_greedy = {h: greedy[h][0] for h in order}
    cut = tuple(sorted(h for h in order if len(h) == 2))
    below = {c: tuple(h for h in order if h[:2] == c) for c in cut}
    decompositions = set()
    enumerated_best = None
    root_optimal = 0
    all_history_optimal = 0
    total_policies = 0
    slack_checks = 0
    for choices in product(*(decisions[h].actions for h in order)):
        policy = dict(zip(order, choices))
        payoff, occupancy, _ = direct_path_value(decisions, terminal, policy)
        enumerated_best = payoff if enumerated_best is None else max(enumerated_best, payoff)
        slack = sum(
            (occupancy[h] * (values[h] - qs[h][policy[h]]) for h in order), F(0)
        )
        assert all(values[h] - qs[h][policy[h]] >= 0 for h in order)
        assert values[()] - payoff == slack
        positive_greedy = all(
            occupancy[h] == 0 or policy[h] in greedy[h] for h in order
        )
        assert (payoff == values[()]) == positive_greedy
        root_optimal += payoff == values[()]
        all_history_optimal += all(policy[h] in greedy[h] for h in order)
        slack_checks += 1
        total_policies += 1

        # One canonical all-raw tree is split at its four retained cut nodes.
        # Reassembly is literal readdressing and retains unchosen subtrees.
        pieces = tuple(tuple(policy[h] for h in below[c]) for c in cut)
        decomposition = (policy[()], pieces)
        decompositions.add(decomposition)
        recovered = {(): policy[()]}
        for c, local_choices in zip(cut, pieces):
            recovered.update(zip(below[c], local_choices))
        assert recovered == policy

    assert total_policies == 8192
    assert len(decompositions) == total_policies
    assert enumerated_best == values[()] == F(2)
    assert root_optimal == 1024
    assert all_history_optimal == 1

    zero_witness = dict(all_greedy)
    zero_witness[("B", "1")] = "skip"
    zero_payoff, zero_occupancy, zero_paths = direct_path_value(
        decisions, terminal, zero_witness
    )
    assert zero_payoff == values[()]
    assert zero_occupancy[("B", "1")] == 0
    assert zero_witness[("B", "1")] not in greedy[("B", "1")]
    assert any(mass == 0 for _, mass, _ in zero_paths)

    off_policy_witness = dict(all_greedy)
    off_policy_witness[("A", "0")] = "skip"
    off_payoff, off_occupancy, _ = direct_path_value(
        decisions, terminal, off_policy_witness
    )
    assert off_payoff == values[()]
    assert off_occupancy[("A", "0")] == 0
    assert off_policy_witness[("A", "0")] not in greedy[("A", "0")]

    # A one-step prefix followed by its complete retained suffix family.
    cut_values = {c: values[c] for c in cut}
    cut_composite_value = max(
        sum((e.probability * (e.reward + cut_values[e.child])
             for e in decisions[()].rows[a]), F(0))
        for a in decisions[()].actions
    )
    assert cut_composite_value == enumerated_best
    return {
        "status": "pass",
        "arena_depth": 3,
        "retained_decision_histories": len(order),
        "retained_terminal_histories": len(terminal),
        "total_policies_enumerated": total_policies,
        "slack_identities_checked": slack_checks,
        "cut_decompositions_checked": len(decompositions),
        "backward_optimal_root_value": values[()],
        "independently_enumerated_optimal_root_value": enumerated_best,
        "cut_composite_value": cut_composite_value,
        "root_action_values": qs[()],
        "root_optimal_total_policies": root_optimal,
        "all_history_greedy_total_policies": all_history_optimal,
        "zero_branch_witness": {
            "changed_history": "B/1",
            "changed_action": "skip",
            "local_greedy_action": "prepare",
            "occupancy": zero_occupancy[("B", "1")],
            "root_value": zero_payoff,
            "mechanism": "Retained raw witness has zero probability under selected root action B.",
        },
        "off_policy_witness": {
            "changed_history": "A/0",
            "changed_action": "skip",
            "local_greedy_action": "prepare",
            "occupancy": off_occupancy[("A", "0")],
            "root_value": off_payoff,
            "mechanism": "The root policy selects B, so the A subtree is off-policy.",
        },
        "scope": "Exact enumeration of this finite all-history arena; not a theorem about arbitrary native feedback.",
    }


def weighted_score(p, table, scores):
    return sum((p[k] * scores[k][table[k]] for k in range(len(p))), F(0))


def cut_rectangularity_diagnostic():
    tables = tuple(product((0, 1), repeat=2))
    families = [tuple(tables[i] for i in range(4) if mask & (1 << i))
                for mask in range(1, 16)]
    laws = ((F(1, 2), F(1, 2)), (F(1), F(0)), (F(0), F(1)))
    binary_scores = tuple(
        ((F(bits[0]), F(bits[1])), (F(bits[2]), F(bits[3])))
        for bits in product((0, 1), repeat=4)
    )
    family_law_cases = 0
    score_comparisons = 0
    for p in laws:
        positive = tuple(k for k, probability in enumerate(p) if probability > 0)
        full_projection = set(product((0, 1), repeat=len(positive)))
        for family in families:
            projected = {tuple(table[k] for k in positive) for table in family}
            rectangle = projected == full_projection
            equality_for_binary_scores = True
            for scores in binary_scores:
                constrained = max(weighted_score(p, table, scores) for table in family)
                unconstrained = sum((p[k] * max(scores[k]) for k in range(2)), F(0))
                assert constrained <= unconstrained
                # Fixed-score equality has an exact feasible-maximizer witness.
                contains_positive_maximizer = any(
                    all(scores[k][table[k]] == max(scores[k]) for k in positive)
                    for table in family
                )
                assert (constrained == unconstrained) == contains_positive_maximizer
                equality_for_binary_scores &= constrained == unconstrained
                score_comparisons += 1
            assert equality_for_binary_scores == rectangle
            family_law_cases += 1

    diagonal_tables = ((0, 0), (1, 1))
    opposed_scores = ((F(1), F(0)), (F(0), F(1)))
    positive_law = (F(1, 2), F(1, 2))
    constrained = max(weighted_score(positive_law, t, opposed_scores) for t in diagonal_tables)
    rectangle_value = sum((positive_law[k] * max(opposed_scores[k]) for k in range(2)), F(0))
    assert constrained == F(1, 2)
    assert rectangle_value == 1
    zero_law = (F(1), F(0))
    assert all(
        max(weighted_score(zero_law, t, scores) for t in diagonal_tables)
        == sum((zero_law[k] * max(scores[k]) for k in range(2)), F(0))
        for scores in binary_scores
    )
    return {
        "status": "pass",
        "nonempty_suffix_families": len(families),
        "prefix_laws": laws,
        "family_law_cases": family_law_cases,
        "binary_score_comparisons": score_comparisons,
        "fixed_score_equality_witness_checks": score_comparisons,
        "strict_obstruction": {
            "prefix_law": positive_law,
            "admitted_suffix_tables": diagonal_tables,
            "local_scores": opposed_scores,
            "constrained_value": constrained,
            "independent_Bellman_value": rectangle_value,
        },
        "zero_coordinate_boundary": {
            "prefix_law": zero_law,
            "admitted_suffix_tables": diagonal_tables,
            "full_raw_table_count": 4,
            "admitted_table_count": 2,
            "scalar_equality_for_all_16_binary_score_tables": True,
            "positive_coordinate_projection_is_full": True,
        },
        "scope": "All nonempty subsets of two binary cut-coordinate tables and three prefix laws. Indicator scores separate omitted positive-coordinate tuples; the general real-score theorem is proved separately.",
    }


def naive_associativity_diagnostic():
    group_h_with_g = tuple(product((0, 1), repeat=2))
    group_g_with_f = ((0, 0), (1, 1))

    def probability_of_one(policy):
        return F(policy[0] + policy[1], 2)

    hg_f_laws = {probability_of_one(p) for p in group_h_with_g}
    h_gf_laws = {probability_of_one(p) for p in group_g_with_f}
    assert hg_f_laws == {F(0), F(1, 2), F(1)}
    assert h_gf_laws == {F(0), F(1)}
    sample_values = (F(-2), F(-1, 2), F(0), F(1, 3), F(2))
    checked = 0
    for v0, v1 in product(sample_values, repeat=2):
        left = max((1 - q) * v0 + q * v1 for q in hg_f_laws)
        right = max((1 - q) * v0 + q * v1 for q in h_gf_laws)
        assert left == right == max(v0, v1)
        checked += 1
    return {
        "status": "pass",
        "construction": "f emits a fair bit; g forgets it to a singleton; h chooses output bit 0 or 1. Naive control substitution uses an action and a full table indexed only by the next external interface.",
        "policies_for_(h_after_g)_after_f": group_h_with_g,
        "policies_for_h_after_(g_after_f)": group_g_with_f,
        "policy_counts": [len(group_h_with_g), len(group_g_with_f)],
        "attainable_P_output_1": {
            "group_h_with_g": sorted(hg_f_laws),
            "group_g_with_f": sorted(h_gf_laws),
        },
        "terminal_score_pairs_checked": checked,
        "common_optimal_value_formula": "max(v(0), v(1))",
        "algebraic_reason": "Each expected value is a convex combination of v(0), v(1), and both constant-output policies are available in each bracketing.",
        "obstruction": "The policy sets have different cardinalities and different attainable output-law sets, even though their optimized terminal-value transformers agree.",
        "repair_scope": "Canonical full-history tree grafting retains the earlier bit at the controller cut; an actual read restriction cannot be removed by rebracketing.",
    }


def shared_demand_diagnostic():
    laws = {
        "independent": {(0, 0): F(1, 4), (0, 1): F(1, 4), (1, 0): F(1, 4), (1, 1): F(1, 4)},
        "common_shock": {(0, 0): F(1, 2), (0, 1): F(0), (1, 0): F(0), (1, 1): F(1, 2)},
    }
    outputs = {}
    for name, law in laws.items():
        marginals = tuple(sum((p for d, p in law.items() if d[i]), F(0)) for i in (0, 1))
        assert marginals == (F(1, 2), F(1, 2))
        costs = {
            c: F(3, 4) * c + 2 * sum((p for d, p in law.items() if sum(d) > c), F(0))
            for c in (1, 2)
        }
        opt = tuple(c for c in costs if costs[c] == min(costs.values()))
        outputs[name] = {
            "raw_joint_law": [{"demand": d, "probability": p} for d, p in law.items()],
            "marginal_P_demand_1": marginals,
            "costs": costs,
            "minimizing_capacities": opt,
        }
    assert outputs["independent"]["costs"] == {1: F(5, 4), 2: F(3, 2)}
    assert outputs["common_shock"]["costs"] == {1: F(7, 4), 2: F(3, 2)}
    assert outputs["independent"]["minimizing_capacities"] == (1,)
    assert outputs["common_shock"]["minimizing_capacities"] == (2,)
    return {
        "status": "pass",
        "criterion": "J(c) = 3*c/4 + 2*P(D1+D2 > c), c in {1,2}",
        "cases": outputs,
        "obstruction": "Identical component demand marginals do not determine the joint capacity decision.",
    }


def native_map_diagnostic():
    terminal_value = F(2, 3)
    source_values = {"safe": terminal_value}
    target_values = {"safe": terminal_value, "better": 1 + terminal_value}
    control_map = {"safe": "safe"}
    # The source has two fair raw atoms, each sent to the target singleton.
    source_raw_law = {"s0": F(1, 2), "s1": F(1, 2)}
    raw_map = {"s0": "t", "s1": "t"}
    pushed = {"t": sum(source_raw_law.values(), F(0))}
    assert pushed == {"t": F(1)}
    assert all(source_values[a] == target_values[control_map[a]] for a in source_values)
    assert max(source_values.values()) < max(target_values.values())

    duplicate_target = {"safe": terminal_value, "duplicate": terminal_value}
    dominated_target = {"safe": terminal_value, "dominated": terminal_value - 1}
    assert max(source_values.values()) == max(duplicate_target.values())
    assert max(source_values.values()) == max(dominated_target.values())
    assert set(control_map.values()) != set(duplicate_target)
    assert set(control_map.values()) != set(dominated_target)

    onto = {"a": "low", "b": "high", "c": "high"}
    target_onto_values = {"low": terminal_value, "high": 2 + terminal_value}
    source_onto_values = {a: target_onto_values[b] for a, b in onto.items()}
    target_opt = {a for a, v in target_onto_values.items() if v == max(target_onto_values.values())}
    source_opt = {a for a, v in source_onto_values.items() if v == max(source_onto_values.values())}
    assert source_opt == {a for a, b in onto.items() if b in target_opt} == {"b", "c"}

    # Native missing-middle obstruction with reward carried by actual laws.
    # The first pair (X,Y) has D/A coupling. The second pair (U,V) has
    # diagonal/antidiagonal coupling. Its pointwise reward is 1[U == V].
    # Every row retains all 16 raw atoms, including its 12 zero atoms.
    D = {(0, 0): F(1, 2), (0, 1): F(0), (1, 0): F(0), (1, 1): F(1, 2)}
    A = {(0, 0): F(0), (0, 1): F(1, 2), (1, 0): F(1, 2), (1, 1): F(0)}
    for q in (D, A):
        assert tuple(sum((p for bits, p in q.items() if bits[i]), F(0)) for i in (0, 1)) == (F(1, 2), F(1, 2))
    raw4 = tuple(product((0, 1), repeat=4))
    raw2 = tuple(product((0, 1), repeat=2))
    first_pair_laws = {"D": D, "A": A}
    target_laws = {"good": D, "bad": A}
    menu = tuple(product(("D", "A"), ("good", "bad")))
    four_bit_laws = {
        control: {
            bits: first_pair_laws[control[0]][bits[:2]] * target_laws[control[1]][bits[2:]]
            for bits in raw4
        }
        for control in menu
    }
    reward4 = {bits: F(bits[2] == bits[3]) for bits in raw4}
    reward2 = {bits: F(bits[0] == bits[1]) for bits in raw2}
    f_raw = {bits: bits for bits in raw4}
    g_raw = {bits: bits[2:] for bits in raw4}

    def push_law(law, raw_function, target_raw):
        result = {bits: F(0) for bits in target_raw}
        for bits, probability in law.items():
            result[raw_function[bits]] += probability
        return result

    f_laws = {control: push_law(q, f_raw, raw4) for control, q in four_bit_laws.items()}
    g_laws = {control: push_law(q, g_raw, raw2) for control, q in four_bit_laws.items()}
    gf_laws = {control: push_law(q, g_raw, raw2) for control, q in f_laws.items()}
    for control, q in four_bit_laws.items():
        assert set(q) == set(raw4)
        assert sum(q.values(), F(0)) == 1
        assert sum(probability == 0 for probability in q.values()) == 12
        assert tuple(sum((p for bits, p in q.items() if bits[i]), F(0)) for i in range(4)) == (F(1, 2),) * 4
        assert f_laws[control] == q
        assert g_laws[control] == target_laws[control[1]]
        assert gf_laws[control] == g_laws[control]
    for q in target_laws.values():
        assert set(q) == set(raw2)
        assert sum(q.values(), F(0)) == 1
        assert sum(probability == 0 for probability in q.values()) == 2
    assert all(reward4[bits] == reward4[f_raw[bits]] for bits in raw4)
    assert all(reward4[bits] == reward2[g_raw[bits]] for bits in raw4)

    def row_reward(law, reward):
        return sum((p * reward[bits] for bits, p in law.items()), F(0))

    four_bit_returns = {control: row_reward(q, reward4) for control, q in four_bit_laws.items()}
    target_returns = {control: row_reward(q, reward2) for control, q in target_laws.items()}
    assert target_returns == {"good": F(1), "bad": F(0)}
    assert all(four_bit_returns[control] == target_returns[control[1]] for control in menu)

    source_policies = tuple(product(menu, repeat=2))
    middle_policies = menu
    target_policies = ("good", "bad")
    # Compatibility is computed from complete law transport, not from tags.
    Rf = {(p, m) for p in source_policies for m in middle_policies
          if all(f_laws[p[i]] == four_bit_laws[m] for i in (0, 1))}
    Rg = {(m, t) for m in middle_policies for t in target_policies
          if g_laws[m] == target_laws[t]}
    Rgf = {(p, t) for p in source_policies for t in target_policies
           if all(gf_laws[p[i]] == target_laws[t] for i in (0, 1))}
    RgRf = {(p, t) for p in source_policies for t in target_policies
            if any((p, m) in Rf and (m, t) in Rg for m in middle_policies)}
    assert RgRf < Rgf
    chosen = (("D", "good"), ("A", "good"))
    assert (chosen, "good") in Rgf
    assert not any((chosen, m) in Rf for m in middle_policies)

    def source_return(p):
        return (four_bit_returns[p[0]] + four_bit_returns[p[1]]) / 2

    source_optimal = {p for p in source_policies if source_return(p) == 1}
    optimal_composite = {(p, t) for p, t in Rgf if p in source_optimal and t == "good"}
    optimal_via_middle = {(p, t) for p, t in RgRf if p in source_optimal and t == "good"}
    assert len(optimal_composite) == 4 and len(optimal_via_middle) == 2
    assert source_return(chosen) == 1
    return {
        "status": "pass",
        "strict_one_step_comparison": {
            "terminal_value": terminal_value,
            "source_action_values": source_values,
            "target_action_values": target_values,
            "control_map": control_map,
            "source_raw_law": source_raw_law,
            "raw_map": raw_map,
            "pushed_raw_law": pushed,
            "source_Bellman_value": max(source_values.values()),
            "target_Bellman_value": max(target_values.values()),
        },
        "coverage_is_not_necessary_for_value_equality": {
            "duplicate_target_action_values": duplicate_target,
            "dominated_target_action_values": dominated_target,
            "value_equality": True,
            "control_map_is_onto": False,
        },
        "onto_one_step_map": {
            "control_map": onto,
            "source_optimal_actions": sorted(source_opt),
            "target_optimal_actions": sorted(target_opt),
            "optimal_source_is_preimage_of_optimal_target": True,
        },
        "missing_middle_with_nonconstant_reward": {
            "source_policy_count": len(source_policies),
            "middle_policy_count": len(middle_policies),
            "target_policy_count": len(target_policies),
            "compatible_composite_pairs": len(Rgf),
            "pairs_factoring_through_middle": len(RgRf),
            "compatible_optimal_composite_pairs": len(optimal_composite),
            "optimal_pairs_factoring_through_middle": len(optimal_via_middle),
            "chosen_source_policy": chosen,
            "chosen_target_policy": "good",
            "chosen_source_return": source_return(chosen),
            "chosen_pair_has_middle_policy": False,
            "source_root_law": [F(1, 2), F(1, 2)],
            "root_rewards": [0, 0],
            "terminal_rewards": 0,
            "source_middle_raw_coordinates": ["X", "Y", "U", "V"],
            "target_raw_coordinates": ["U", "V"],
            "pointwise_source_reward": "1[U=V]",
            "pointwise_target_reward": "1[U=V]",
            "pointwise_reward_preservation_checks": len(raw4),
            "all_rows_normalized": True,
            "all_source_primitive_bits_are_fair": True,
            "all_target_primitive_bits_are_fair": True,
            "source_middle_rows": [
                {
                    "control": control,
                    "expected_reward": four_bit_returns[control],
                    "total_mass": sum(q.values(), F(0)),
                    "marginal_P_bit_1": [sum((p for bits, p in q.items() if bits[i]), F(0)) for i in range(4)],
                    "zero_atom_count": sum(p == 0 for p in q.values()),
                    "raw_atoms": [{"raw": bits, "probability": q[bits], "reward": reward4[bits]} for bits in raw4],
                }
                for control, q in four_bit_laws.items()
            ],
            "target_rows": [
                {
                    "control": control,
                    "expected_reward": target_returns[control],
                    "total_mass": sum(q.values(), F(0)),
                    "marginal_P_bit_1": [sum((p for bits, p in q.items() if bits[i]), F(0)) for i in range(2)],
                    "zero_atom_count": sum(p == 0 for p in q.values()),
                    "raw_atoms": [{"raw": bits, "probability": q[bits], "reward": reward2[bits]} for bits in raw2],
                }
                for control, q in target_laws.items()
            ],
            "f_raw_map": [{"source": bits, "target": f_raw[bits]} for bits in raw4],
            "g_raw_map": [{"source": bits, "target": g_raw[bits]} for bits in raw4],
            "relations_derived_from_full_law_pushforward": True,
            "mechanism": "The first map merges the two fair root histories and is identity on all four-bit raw rows. The second projects (X,Y,U,V) to (U,V), preserving 1[U=V] on every raw atom. The omitted first two target coordinates can equivalently be retained as singletons. Good and bad are actual diagonal/antidiagonal laws of (U,V), not reward tags. Each four-bit law is the independent product of a D/A law on (X,Y) and the selected law on (U,V). Optimizing the nonconstant pointwise reward leaves the D/A descent obstruction intact.",
        },
        "scope": "Finite row/control and policy-relation witnesses with unit material coefficients; no automatic lifting of arbitrary native maps is inferred.",
    }


def horizon_diagnostic():
    # Two decisions remain at t=0. Setup costs 1. Completion at t=1 pays 3
    # only if setup was performed at t=0. There is no terminal salvage value.
    actions = {
        (0, "unready"): {"setup": (F(-1), "ready"), "wait": (F(0), "unready")},
        (1, "unready"): {"setup": (F(-1), "ready"), "wait": (F(0), "unready")},
        (1, "ready"): {"finish": (F(3), "done"), "wait": (F(0), "ready")},
    }
    suffix = {
        state: max(r for r, _ in actions[(1, state)].values())
        for state in ("ready", "unready")
    }
    complete_scores = {a: r + suffix[next_state]
                       for a, (r, next_state) in actions[(0, "unready")].items()}
    complete_best = max(complete_scores.values())
    assert complete_scores == {"setup": F(2), "wait": F(0)}
    state = "unready"
    rolling_return = F(0)
    rolling_actions = []
    for t in (0, 1):
        menu = actions[(t, state)]
        best = max(r for r, _ in menu.values())
        selected = tuple(a for a, (r, _) in menu.items() if r == best)
        assert len(selected) == 1
        a = selected[0]
        reward, state = menu[a]
        rolling_return += reward
        rolling_actions.append(a)
    assert complete_best == 2
    assert rolling_return == 0
    return {
        "status": "pass",
        "complete_two_step_action_values": complete_scores,
        "correct_cut_continuation_values": suffix,
        "complete_two_step_optimal_return": complete_best,
        "rolling_one_step_terminal_value": 0,
        "rolling_one_step_actions": rolling_actions,
        "rolling_one_step_return": rolling_return,
        "obstruction": "Restarting a shorter optimization with zero terminal evaluation changes the objective at the cut. It is not the Bellman decomposition of the original two-step problem.",
        "scope": "A finite deterministic horizon-truncation example, not an infinite-horizon stability or convergence result.",
    }


def run_all():
    checks = {
        "full_history_arena": arena_diagnostic(),
        "cut_rectangularity": cut_rectangularity_diagnostic(),
        "naive_policy_associativity": naive_associativity_diagnostic(),
        "shared_demand": shared_demand_diagnostic(),
        "native_maps_and_policy_descent": native_map_diagnostic(),
        "replanning_horizon": horizon_diagnostic(),
    }
    assert all(item["status"] == "pass" for item in checks.values())
    return {
        "artifact": "Prospective Interaction finite diagnostics",
        "status": "pass",
        "arithmetic": "fractions.Fraction throughout; no floating-point comparisons",
        "assertions_enabled": __debug__,
        "python": sys.version.split()[0],
        "evidence_class": "Executed exact finite diagnostics; no proof-assistant certification and no general native-lift claim.",
        "checks": checks,
    }


def main():
    if not __debug__:
        raise SystemExit("Diagnostics require Python assertions; rerun without -O or -OO.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    parser.add_argument("--full", action="store_true", help="Print the complete result JSON as well as saving it.")
    args = parser.parse_args()
    result = encode(run_all())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.full:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(json.dumps({
            "status": result["status"],
            "output": str(args.output),
            "policies_enumerated": result["checks"]["full_history_arena"]["total_policies_enumerated"],
            "root_optimal_policies": result["checks"]["full_history_arena"]["root_optimal_total_policies"],
            "all_history_greedy_policies": result["checks"]["full_history_arena"]["all_history_greedy_total_policies"],
            "cut_score_comparisons": result["checks"]["cut_rectangularity"]["binary_score_comparisons"],
            "check_groups": len(result["checks"]),
        }, sort_keys=True))


if __name__ == "__main__":
    main()
