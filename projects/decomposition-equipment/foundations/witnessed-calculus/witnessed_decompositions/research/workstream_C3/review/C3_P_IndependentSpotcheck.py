#!/usr/bin/env python3
"""Non-author proof-audit checks. No imports from the author implementation.

These finite reconstructions support the P review; they do not prove its
arbitrary-size or arbitrary-signature statements or replace the separate C gate.
"""
import itertools
import json


def restrict(graph, vertices):
    n, edges = graph
    vertices = tuple(sorted(vertices))
    assert len(set(vertices)) == len(vertices)
    assert all(0 <= v < n for v in vertices)
    positions = {v: i for i, v in enumerate(vertices)}
    return (len(vertices), frozenset(
        (positions[x], positions[y]) for x, y in edges
        if x in positions and y in positions))


BLOCKS = ((0,), (1, 3), (2, 4), (5,))
OBJECTS = (0, 1, 1, 1, 2)
H = (2, frozenset({(0, 1)}))
Q = (1, frozenset())


def descendants(shape):
    if isinstance(shape, int):
        return (shape,)
    return descendants(shape[0]) + descendants(shape[1])


def construct(graph, shape):
    indices = descendants(shape)
    support = tuple(sorted(v for i in indices for v in BLOCKS[i]))
    whole = restrict(graph, support)
    grade = (OBJECTS[indices[0]], OBJECTS[indices[-1] + 1])
    if isinstance(shape, int):
        return ("identity", whole, grade)
    rank = {v: i for i, v in enumerate(support)}
    parts = tuple(tuple(sorted(rank[v] for i in descendants(child)
                              for v in BLOCKS[i])) for child in shape)
    children = tuple(construct(graph, child) for child in shape)
    return ("primitive", whole, grade, parts, children)


def evaluate(tree):
    kind, graph, grade = tree[:3]
    if kind == "identity":
        return graph, grade, ((graph, grade),), (tuple(range(graph[0])),)
    _, _, _, parts, children = tree
    results = tuple(evaluate(child) for child in children)
    assert len(parts) == len(results) == 2
    assert results[0][1][0] == grade[0]
    assert results[0][1][1] == results[1][1][0]
    assert results[1][1][1] == grade[1]
    profile, final = [], []
    for part, (child_graph, child_grade, child_profile, child_blocks) in zip(parts, results):
        assert restrict(graph, part) == child_graph
        assert child_grade[0] <= child_grade[1]
        profile.extend(child_profile)
        final.extend(tuple(part[j] for j in block) for block in child_blocks)
    return graph, grade, tuple(profile), tuple(final)


def relation_compose(r, s):
    return frozenset((x, z) for x, y in r for yy, z in s if y == yy)


def powerset(items):
    items = tuple(items)
    for mask in range(1 << len(items)):
        yield frozenset(items[i] for i in range(len(items)) if mask & (1 << i))


def main():
    all_edges = frozenset(itertools.combinations(range(6), 2))
    internal = frozenset({(1, 3), (2, 4)})
    cross = all_edges - internal
    assert len(cross) == 13
    expected_profile = ((Q, (0, 1)), (H, (1, 1)), (H, (1, 1)), (Q, (1, 2)))
    graphs_seen = set()
    for cross_subset in powerset(sorted(cross)):
        graph = (6, internal | cross_subset)
        assert tuple(restrict(graph, b) for b in BLOCKS) == (Q, H, H, Q)
        assert graph[1] & cross == cross_subset
        graphs_seen.add(graph)
        balanced = construct(graph, ((0, 1), (2, 3)))
        right = construct(graph, (0, (1, (2, 3))))
        assert balanced != right
        expected = (graph, (0, 2), expected_profile, BLOCKS)
        assert evaluate(balanced) == expected == evaluate(right)
    assert len(graphs_seen) == 8192

    # Actual primitive labels differ while both children have the same type.
    children = (("identity", Q, (1, 1)),) * 2
    u_tree = ("primitive", H, (1, 1), ((0,), (1,)), children)
    v_tree = ("primitive", H, (1, 1), ((1,), (0,)), children)
    u, v = evaluate(u_tree), evaluate(v_tree)
    assert u_tree != v_tree and u != v and u[:3] == v[:3]
    assert u[0][1] == v[0][1] == frozenset({(0, 1)})
    replacement_blocks = (((0,),), u[3], v[3], ((0,),))
    refined = tuple(tuple(parent[j] for j in child)
                    for parent, children in zip(BLOCKS, replacement_blocks)
                    for child in children)
    assert refined == ((0,), (1,), (3,), (4,), (2,), (5,))
    for erroneous in ((u[3], u[3]), (v[3], v[3])):
        choices = (((0,),), *erroneous, ((0,),))
        bad = tuple(tuple(parent[j] for j in child)
                    for parent, children in zip(BLOCKS, choices)
                    for child in children)
        assert bad != refined

    # Independently enumerate ambient assignments for the unanchored factor.
    placements = [labels for labels in itertools.product(range(4), repeat=6)
                  if tuple(labels.count(i) for i in range(4)) == (1, 2, 2, 1)]
    assert len(placements) == 180
    assert len(placements) * len(graphs_seen) == 1474560

    r = frozenset({(0, 0), (0, 1), (1, 2)})
    s = frozenset({(0, 0), (1, 0), (2, 1)})
    d = frozenset({(0, 0), (1, 1)})
    w = frozenset(itertools.product(range(2), repeat=2))
    assert relation_compose(r, s) == d and d < w
    r1 = frozenset({(0, 0), (1, 1), (1, 2)})
    obs = lambda rel: (frozenset(x for x, _ in rel), frozenset(y for _, y in rel))
    assert r != r1 and obs(r) == obs(r1)

    matrices = images = candidates = 0
    for a in range(3):
        for b in range(4):
            fibres = {}
            for rel in powerset(itertools.product(range(a), range(b))):
                fibres.setdefault(obs(rel), []).append(rel)
                matrices += 1
            images += len(fibres)
            for left in powerset(range(a)):
                for right in powerset(range(b)):
                    candidates += 1
                    fibre = fibres.get((left, right), [])
                    exists = bool(left) == bool(right)
                    assert bool(fibre) == exists
                    if exists:
                        singleton = not left or min(len(left), len(right)) == 1
                        assert (len(fibre) == 1) == singleton
                        exact = [rel for rel in powerset(itertools.product(left, right))
                                 if all(any(x == xx for xx, y in rel) for x in left)
                                 and all(any(y == yy for x, yy in rel) for y in right)]
                        assert set(fibre) == set(exact)
    assert (matrices, candidates, images) == (104, 105, 56)
    return {
        "status": "PASS",
        "role": "Independent auxiliary P-proof certificate reconstruction, not unrestricted proof or final C acceptance",
        "six_vertex_graphs_and_typed_grouping_pairs": len(graphs_seen),
        "unanchored_block_placements": len(placements),
        "unanchored_witness_count_by_verified_factor": len(placements) * len(graphs_seen),
        "opposite_cut_and_occurrence_checks": "PASS",
        "relation_composite_and_support_collision": "PASS",
        "relation_matrices": matrices,
        "support_candidates": candidates,
        "nonempty_support_fibres": images,
    }


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
