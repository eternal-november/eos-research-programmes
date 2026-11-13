#!/usr/bin/env python3
"""Independent finite checks of the exceptional unit-tree boundary.

Pure Python, no imports of prior verification code.  These checks distinguish
positive-vertex factor trees from the vertex-free tree.  They do not choose
the intended admissible grammar or prove the unbounded tree theorems.
"""

import argparse
from collections import defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without -O; assertions are part of this checker")

HERE = Path(__file__).resolve().parent
DEFAULT_SOURCE_ROOT = HERE / "sources"


def canonical_partition(blocks):
    return tuple(sorted((tuple(sorted(b)) for b in blocks)))


def refine_binary(table, identity, seed, observe_unit):
    """Refine actual SETS of states, not a copy of the previous checker."""
    blocks = canonical_partition(seed)
    history = [len(blocks)]
    while True:
        cls = {x: i for i, block in enumerate(blocks) for x in block}
        fibres = [set() for _ in table]
        for a, row in enumerate(table):
            for b, x in enumerate(row):
                fibres[x].add((cls[a], cls[b]))
        next_blocks = []
        for block in blocks:
            buckets = defaultdict(list)
            for x in block:
                # {} versus {()} is the zero-factor record signature.
                unit_signature = (x == identity) if observe_unit else None
                buckets[(frozenset(fibres[x]), unit_signature)].append(x)
            next_blocks.extend(buckets.values())
        new = canonical_partition(next_blocks)
        if new == blocks:
            return {"stage_counts": history, "partition": blocks}
        blocks = new
        history.append(len(blocks))


def c4_tests():
    # Additive C4 -> C2, h(x)=x mod 2.  Zero vertices means empty sum = 0.
    chains = []
    for vertices in range(1, 7):
        actual = defaultdict(set)
        for labels in product(range(4), repeat=vertices):
            actual[sum(labels) % 4].add(tuple(x % 2 for x in labels))
        checked = 0
        for source in range(4):
            expected = {
                target for target in product(range(2), repeat=vertices)
                if sum(target) % 2 == source % 2
            }
            assert actual[source] == expected
            checked += len(expected)
        chains.append({"vertices": vertices, "source_target_records": checked})

    stars = []
    for arity in range(1, 5):
        checked = 0
        for sources in product(range(4), repeat=arity):
            for target_parent in range(2):
                target_children = tuple((x - target_parent) % 2 for x in sources)
                candidates = []
                for parent in range(4):
                    if parent % 2 != target_parent:
                        continue
                    children = tuple((x - parent) % 4 for x in sources)
                    assert all((parent + y) % 4 == x
                               for x, y in zip(sources, children))
                    assert tuple(y % 2 for y in children) == target_children
                    candidates.append(parent)
                assert len(candidates) == 2
                checked += 1
        stars.append({"active_descendants": arity, "source_target_records": checked})

    exceptional = []
    for source in range(4):
        target_has_record = source % 2 == 0
        source_has_record = source == 0
        exceptional.append({"source": source, "target": source % 2,
                            "target_unit_record_exists": target_has_record,
                            "source_unit_record_exists": source_has_record})
    assert exceptional[2]["target_unit_record_exists"]
    assert not exceptional[2]["source_unit_record_exists"]

    # In two channels, all translations followed by literal unit feasibility
    # distinguish all 16 labels already at the fixed unary identity profile.
    states = tuple(product(range(4), repeat=2))
    unit_theories = {
        tuple(((a + g) % 4, (b + h) % 4) == (0, 0) for g, h in states)
        for a, b in states
    }
    assert len(unit_theories) == 16
    quotient_states = {(a % 2, b % 2) for a, b in states}
    assert len(quotient_states) == 4
    return {
        "positive_chain_checks": chains,
        "positive_shared_parent_checks": stars,
        "vertex_free_checks": exceptional,
        "two_channel_counterexample": {"source": [2, 0], "target": [0, 0],
                                       "source_is_identity": False,
                                       "target_is_identity": True},
        "two_channel_parity_state_count": 4,
        "translation_then_unit_theory_state_count": len(unit_theories),
    }


def m4_tests():
    # Transformation convention: (f*g)(i)=f(g(i)).
    def multiply(f, g):
        return tuple(f[g[i]] for i in range(4))
    identity = (0, 1, 2, 3)
    a = (3, 1, 1, 2)
    b = (1, 2, 1, 1)
    elements = {identity, a, b}
    while True:
        grown = elements | {multiply(f, g) for f in elements for g in elements}
        if grown == elements:
            break
        elements = grown
    elements = tuple(sorted(elements))
    index = {x: i for i, x in enumerate(elements)}
    table = [[index[multiply(f, g)] for g in elements] for f in elements]
    assert len(elements) == 10
    assert all(table[table[x][y]][z] == table[x][table[y][z]]
               for x, y, z in product(range(10), repeat=3))
    unit = index[identity]
    assert all(table[unit][x] == x == table[x][unit] for x in range(10))
    H = {identity, b, multiply(b, b)}
    seed = [[i for i, x in enumerate(elements) if x in H],
            [i for i, x in enumerate(elements) if x not in H]]
    binary = refine_binary(table, unit, seed, False)
    with_unit = refine_binary(table, unit, seed, True)
    top = refine_binary(table, unit, [list(range(10))], True)
    assert binary["stage_counts"] == [2, 3, 4]
    assert with_unit["stage_counts"] == [2, 4, 6, 8]
    assert top["stage_counts"] == [1, 2, 3, 6, 8]
    assert any(unit in B and index[b] in B for B in binary["partition"])
    assert not any(unit in B and index[b] in B for B in with_unit["partition"])
    for result in (binary, with_unit, top):
        result["partition"] = [[elements[i] for i in block] for block in result["partition"]]
    return {"monoid_size": len(elements), "identity": identity, "a": a, "b": b,
            "binary_only_H_seed": binary, "binary_plus_unit_H_seed": with_unit,
            "binary_plus_unit_top_seed": top,
            "comparison_to_previous_probe": "Same M4 stage counts; independently implemented"}


def cyclic_group_map_tests():
    rows = []
    for n in range(1, 9):
        for m in range(1, 9):
            for generator_image in range(m):
                if n * generator_image % m:
                    continue
                h = lambda x: (x * generator_image) % m
                surjective = {h(x) for x in range(n)} == set(range(m))
                identity_reflecting = [x for x in range(n) if h(x) == 0] == [0]
                positive = all(
                    any(h(a) == q and h(b) == r and (a + b) % n == x
                        for a, b in product(range(n), repeat=2))
                    for x in range(n) for q, r in product(range(m), repeat=2)
                    if (q + r) % m == h(x)
                )
                unit = all(h(x) != 0 or x == 0 for x in range(n))
                assert positive == surjective
                assert unit == identity_reflecting
                assert (positive and unit) == (surjective and len(set(map(h, range(n)))) == n)
                rows.append({"source_order": n, "target_order": m,
                             "generator_image": generator_image,
                             "positive_binary_all_source_lifting": positive,
                             "unit_all_source_lifting": unit})
    return {"tested_homomorphisms": len(rows),
            "all_corrected_criterion_checks_pass": True, "cases": rows}


def source_manifest(source_root):
    paths = [
        "i5_joint_repair_20261031/model_and_core_comparison.md",
        "i5_joint_repair_20261031/concrete_model_gate.md",
        "i5_joint_repair_20261031/i5_joint_repair_theorem.md",
        "i2_minimal_realization_20261031/i2_minimal_realization_theorem.md",
        "i1_amalgamation_20261031/cut_transport_draft.md",
        "i1_amalgamation_20261031/dependencies/Semantics_Transport_Factorization.md",
        "final_acceptance_review_20261101/adversarial/i5_vertex_free_control_results.json",
    ]
    return [{"path": p, "sha256": sha256((source_root / p).read_bytes()).hexdigest()}
            for p in paths]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=DEFAULT_SOURCE_ROOT,
                        help="Root containing the seven provenance snapshots; defaults to bundled sources/")
    args = parser.parse_args()
    result = {"status": "Independent finite boundary checks passed",
              "scope": "Conditional on admitting the literal vertex-free unit cut; no grammar decision made",
              "c4_to_c2": c4_tests(), "m4": m4_tests(),
              "cyclic_group_map_survey": cyclic_group_map_tests(),
              "source_manifest": source_manifest(args.source_root),
              "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE / "unit_boundary_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"],
                      "M4_binary": result["m4"]["binary_only_H_seed"]["stage_counts"],
                      "M4_with_unit": result["m4"]["binary_plus_unit_H_seed"]["stage_counts"],
                      "M4_top_with_unit": result["m4"]["binary_plus_unit_top_seed"]["stage_counts"],
                      "cyclic_homomorphisms": result["cyclic_group_map_survey"]["tested_homomorphisms"],
                      "C4_squared_unit_translation_states": 16}, indent=2))


if __name__ == "__main__":
    main()
