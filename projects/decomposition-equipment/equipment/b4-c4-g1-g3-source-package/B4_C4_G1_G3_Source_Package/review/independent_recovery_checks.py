"""Reviewer-owned finite checks, independent of the author encoders.

Finite regression only. The all-size claims are reviewed in mathematical proofs.
"""
from itertools import combinations, permutations, product
from collections import Counter
import hashlib
import json
from pathlib import Path
from math import factorial, prod

if not __debug__:
    raise RuntimeError("Run without -O: assertions are required")

def subsets(xs):
    xs = tuple(xs)
    for bits in product((0, 1), repeat=len(xs)):
        yield frozenset(x for x, bit in zip(xs, bits) if bit)

LEAF = None

def trees(n):
    if n == 0:
        return (LEAF,)
    out = []
    if n == 1:
        out.append(("null", ()))
    for child in trees(n - 1):
        for label in ("u", "v"):
            out.append((label, (child,)))
    for left_n in range(n):
        for left in trees(left_n):
            for right in trees(n - 1 - left_n):
                out.append(("binary", (left, right)))
    return tuple(out)

def addresses(t, internal, a=()):
    if t is None:
        return () if internal else (a,)
    return ((a,) if internal else ()) + tuple(
        b for i, child in enumerate(t[1])
        for b in addresses(child, internal, a + (i,)))

def subtree(t, a):
    for i in a:
        t = t[1][i]
    return t

def prefixes(t):
    yield None
    if t is not None:
        for children in product(*(tuple(prefixes(c)) for c in t[1])):
            yield (t[0], children)

def prefix_count(t):
    if t is None:
        return 1
    ans = 1
    for c in t[1]:
        ans *= prefix_count(c)
    return 1 + ans

def graft(t, forest, a=()):
    if t is None:
        return forest[a]
    return (t[0], tuple(graft(c, forest, a + (i,)) for i, c in enumerate(t[1])))

raw_cases = schedules = independent_pairs = 0
for n in range(5):
    for u in trees(n):
        ps = tuple(prefixes(u))
        assert len(ps) == len(set(ps)) == prefix_count(u)
        assert (len(ps) == 1) == (u is None)
        for t in ps:
            raw_cases += 1
            forest = {a: subtree(u, a) for a in addresses(t, False)}
            assert graft(t, forest) == u
            tv = set(addresses(t, True))
            uv = set(addresses(u, True))
            assert tv <= uv
            assert len(uv) == len(tv) + sum(len(addresses(x, True)) for x in forest.values())
            frontier = tuple(a + b for a, f in forest.items() for b in addresses(f, False))
            assert frontier == addresses(u, False)
            events = tuple(sorted(uv - tv))
            legal = []
            for schedule in permutations(events):
                seen = set(tv)
                good = True
                for a in schedule:
                    if any(a[:j] not in seen for j in range(len(a))):
                        good = False
                        break
                    seen.add(a)
                if good:
                    legal.append(schedule)
            assert legal
            hook_product = prod(sum(b[:len(a)] == a for b in events) for a in events)
            assert len(legal) * hook_product == factorial(len(events))
            schedules += len(legal)
            assert (len(legal) == 1) == all(a[:len(b)] == b or b[:len(a)] == a for a in events for b in events)
            reachable = {legal[0]}
            todo = [legal[0]]
            while todo:
                x = todo.pop()
                for i in range(len(x) - 1):
                    a, b = x[i:i+2]
                    if a[:len(b)] != b and b[:len(a)] != a:
                        y = x[:i] + (b, a) + x[i+2:]
                        assert y in legal
                        independent_pairs += 1
                        if y not in reachable:
                            reachable.add(y)
                            todo.append(y)
            assert reachable == set(legal)

def restrict(edges, block):
    ordered = tuple(sorted(block))
    return frozenset((i, j) for i, j in combinations(range(len(ordered)), 2)
                     if (ordered[i], ordered[j]) in edges)

def decode_by_adjacency(blocks, local_edges, cross_edges):
    """No encoder/table lookup: classify each ambient pair independently."""
    owner = {v: i for i, b in enumerate(blocks) for v in b}
    ranks = {v: j for b in blocks for j, v in enumerate(sorted(b))}
    n = sum(map(len, blocks))
    recovered = set()
    for x, y in combinations(range(n), 2):
        i, j = owner[x], owner[y]
        if i == j:
            if tuple(sorted((ranks[x], ranks[y]))) in local_edges[i]:
                recovered.add((x, y))
        elif (x, y) in cross_edges:
            recovered.add((x, y))
    return frozenset(recovered)

graph_records = fibres = 0
for n in range(5):
    pairs = tuple(combinations(range(n), 2))
    graphs = tuple(subsets(pairs))
    for k in range(5):
        if k == 0 and n:
            continue
        counts = Counter()
        for assignment in product(range(k), repeat=n):
            blocks = tuple(frozenset(v for v in range(n) if assignment[v] == i) for i in range(k))
            cross = frozenset(e for e in pairs if assignment[e[0]] != assignment[e[1]])
            for edges in graphs:
                local = tuple(restrict(edges, b) for b in blocks)
                assert decode_by_adjacency(blocks, local, edges & cross) == edges
                profile = tuple((len(b), h) for b, h in zip(blocks, local))
                counts[profile] += 1
                graph_records += 1
        for profile, count in counts.items():
            sizes = tuple(x[0] for x in profile)
            q = sum(sizes[i] * sizes[j] for i in range(k) for j in range(i+1, k))
            expected = factorial(n) // prod(factorial(s) for s in sizes) * (2 ** q)
            assert count == expected
            fibres += 1

blocks6 = tuple(map(frozenset, ((0,), (1,3), (2,4), (5,))))
local6 = (frozenset(), frozenset({(0,1)}), frozenset({(0,1)}), frozenset())
cross6 = tuple(e for e in combinations(range(6), 2) if not any(set(e) <= b for b in blocks6))
assert len(cross6) == 13
restored6 = set()
for c in subsets(cross6):
    edges = decode_by_adjacency(blocks6, local6, c)
    assert tuple(restrict(edges, b) for b in blocks6) == local6
    assert edges & frozenset(cross6) == c
    restored6.add(edges)
assert len(restored6) == 8192
assert 2 ** 12 < len(restored6) == 2 ** 13
g0 = frozenset({(0,1),(1,2),(1,3),(2,4),(3,4),(4,5)})
g1 = g0 | {(0,5)}
assert tuple(restrict(g0, b) for b in blocks6) == tuple(restrict(g1, b) for b in blocks6)
assert g0 != g1
# Actual repeated-slot refinement uses forward at B1 and reverse at B2.
refined = (frozenset({0}), frozenset({1}), frozenset({3}), frozenset({4}), frozenset({2}), frozenset({5}))
assert tuple(next(iter(b)) for b in refined) == (0,1,3,4,2,5)
assert tuple(next(iter(b)) for b in refined) != (0,1,3,2,4,5)
# Enumerate scalar-decorated actual four-entry tuples, with the local ordered
# partitions explicitly supplied, independently of any solution-vector encoder.
local_splits = (((0,),), ((0,), (1,)), ((1,), (0,)), ((0,),))
arrows = []
for values in product((0, 1), repeat=4):
    entries = tuple((local_splits[i], values[i]) for i in range(4))
    lifted = tuple(frozenset(tuple(sorted(blocks6[i]))[j] for j in part)
                   for i, entry in enumerate(entries) for part in entry[0])
    composite_scalar = sum(entry[1] for entry in entries) % 2
    if lifted == refined and composite_scalar == 0:
        arrows.append(entries)
assert len(arrows) == 8 == 2 ** 3
for bits in product((0, 1), repeat=3):
    inferred = bits + (sum(bits) % 2,)
    decoded_arrow = tuple((local_splits[i], inferred[i]) for i in range(4))
    assert decoded_arrow in arrows
assert len(restored6) * len(arrows) == 2 ** 16
# Empty structural runs really are occurrence data: a nullary/unary tuple and
# a unary/nullary tuple produce the same one-empty-slot target but are distinct.
empty_slot_tuples = (((), ((),)), (((),), ()))
assert empty_slot_tuples[0] != empty_slot_tuples[1]
assert all(tuple(part for entry in t for part in entry) == ((),) for t in empty_slot_tuples)
# In a one-object C2 grade regression, two nonidentity source grades cannot be
# replaced by zero-length paths, despite their total grade being identity.
source_grades = (1, 1)
assert sum(source_grades) % 2 == 0
assert not all(grade == 0 for grade in source_grades)
# C5-native zero/nonzero observation is not stable under +1 in Z/3.
assert bool(1) == bool(2)
assert bool((1+1) % 3) != bool((2+1) % 3)

report = {
    "status": "PASS",
    "evidence_level": "finite reviewer regression, not an unrestricted theorem",
    "raw_max_internal_vertices": 4,
    "raw_source_final_records": raw_cases,
    "legal_atomic_schedules": schedules,
    "independent_swap_edges_examined": independent_pairs,
    "graph_domain": "all ordered simple graphs n=0..4 and k=0..4 labelled block assignments, empty slots retained",
    "graph_partition_records": graph_records,
    "unanchored_profile_fibres": fibres,
    "six_vertex_anchored_graphs": len(restored6),
    "six_vertex_fixed_endpoint_scalar_arrows": len(arrows),
    "combined_topology_scalar_targets": len(restored6) * len(arrows),
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
print(json.dumps(report, indent=2, sort_keys=True))
