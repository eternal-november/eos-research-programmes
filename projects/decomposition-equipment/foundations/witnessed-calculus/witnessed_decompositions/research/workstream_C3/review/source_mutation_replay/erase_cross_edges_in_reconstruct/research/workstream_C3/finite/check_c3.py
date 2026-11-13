#!/usr/bin/env python3
"""C3 finite author certificate: exact frozen domains, standard library only.

Independent review is separate. These computations are C/X evidence, never
an unrestricted proof or an acceptance decision. No inherited evaluator import.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from dataclasses import dataclass
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
import json
from math import factorial, prod
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CONTRACT = '47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET = '88ea710752d99cd83d10c85740f825b1c543d58c0f475615c667020bc1aa2825'


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def powerset(items):
    items = tuple(items)
    for bits in range(1 << len(items)):
        yield frozenset(x for j, x in enumerate(items) if bits >> j & 1)


@dataclass(frozen=True, order=True)
class Graph:
    n: int
    edges: frozenset[tuple[int, int]]

    def __post_init__(self):
        assert self.n >= 0
        assert all(0 <= x < y < self.n for x, y in self.edges)

    def restrict(self, block):
        block = tuple(sorted(block))
        assert len(set(block)) == len(block)
        assert all(0 <= x < self.n for x in block)
        ranks = {x: i for i, x in enumerate(block)}
        return Graph(len(block), frozenset((ranks[x], ranks[y])
                         for x, y in self.edges if x in ranks and y in ranks))

    def code(self):
        return (self.n, tuple(sorted(self.edges)))


def all_graphs(m):
    return tuple(Graph(m, e) for e in powerset(combinations(range(m), 2)))


def partitions(m, k):
    # product(..., repeat=0) has one element even when k=0.
    for labels in product(range(k), repeat=m):
        yield tuple(tuple(v for v in range(m) if labels[v] == i) for i in range(k))


def valid_blocks(m, blocks):
    assert all(tuple(sorted(b)) == b and len(set(b)) == len(b) for b in blocks)
    flattened = [x for b in blocks for x in b]
    assert sorted(flattened) == list(range(m))


def cross_pairs(m, blocks):
    valid_blocks(m, blocks)
    membership = {x: i for i, b in enumerate(blocks) for x in b}
    return tuple((x, y) for x, y in combinations(range(m), 2)
                 if membership[x] != membership[y])


def leaves(g, blocks):
    return tuple(g.restrict(b) for b in blocks)


def matrix_leaves(g, blocks):
    # Redundant authored algorithm: indexed adjacency, not rank dictionary.
    adj = [[False] * g.n for _ in range(g.n)]
    for x, y in g.edges:
        adj[x][y] = adj[y][x] = True
    return tuple(Graph(len(b), frozenset((i, j) for i in range(len(b))
                  for j in range(i + 1, len(b)) if adj[b[i]][b[j]])) for b in blocks)


def reconstruct(h, blocks, cross):
    m = sum(g.n for g in h)
    assert len(h) == len(blocks)
    valid_blocks(m, blocks)
    assert all(g.n == len(b) for g, b in zip(h, blocks))
    assert set(cross) <= set(cross_pairs(m, blocks))
    edges = set()
    for local, b in zip(h, blocks):
        edges.update((b[x], b[y]) for x, y in local.edges)
    return Graph(m, frozenset(edges))


def matrix_reconstruct(h, blocks, cross):
    # Independent formula for every ambient pair; no union/lift helper.
    m = sum(len(b) for b in blocks)
    inverse = {v: (i, j) for i, b in enumerate(blocks) for j, v in enumerate(b)}
    edges = set()
    for x, y in combinations(range(m), 2):
        i, a = inverse[x]
        j, b = inverse[y]
        if ((x, y) in cross if i != j else (min(a, b), max(a, b)) in h[i].edges):
            edges.add((x, y))
    return Graph(m, frozenset(edges))


def chain_strings(k):
    return tuple(combinations_with_replacement(range(3), k + 1))


def graph_fibres():
    counts = defaultdict(int)
    per_size = []
    fibre_hist = defaultdict(int)
    leaf_hist = defaultdict(int)
    case_hash = sha256()
    for m in range(5):
        gs = all_graphs(m)
        row = {'m': m, 'graphs': len(gs), 'partition_assignments': 0,
               'graph_partition_pairs': 0, 'represented_typed_pairs': 0}
        for k in range(6):
            bs = tuple(partitions(m, k))
            unanchored = defaultdict(set)
            for blocks in bs:
                x = cross_pairs(m, blocks)
                sizes = tuple(len(b) for b in blocks)
                exponent = sum(sizes[i] * sizes[j] for i in range(k) for j in range(i + 1, k))
                assert len(x) == exponent
                assert (len(x) == 0) == (sum(n > 0 for n in sizes) <= 1)
                groups = defaultdict(set)
                for g in gs:
                    h = leaves(g, blocks)
                    assert h == matrix_leaves(g, blocks)
                    cross = frozenset(g.edges.intersection(x))
                    assert reconstruct(h, blocks, cross) == g
                    assert matrix_reconstruct(h, blocks, cross) == g
                    groups[h].add(g)
                    unanchored[h].add((blocks, g))
                    counts['anchored_inverse_graph_checks'] += 1
                internal_pairs = sum(n * (n - 1) // 2 for n in sizes)
                assert len(groups) == 2 ** internal_pairs
                for h, members in groups.items():
                    generated = set()
                    for cross in powerset(x):
                        recovered = reconstruct(h, blocks, cross)
                        assert recovered == matrix_reconstruct(h, blocks, cross)
                        assert leaves(recovered, blocks) == h
                        assert recovered.edges.intersection(x) == cross
                        generated.add(recovered)
                        counts['anchored_inverse_cross_checks'] += 1
                    assert generated == members
                    assert len(members) == 2 ** exponent
                    fibre_hist[len(members)] += 1
                    counts['anchored_fibres'] += 1
                    case_hash.update(repr((m, k, blocks, tuple(g.code() for g in h), len(members))).encode())
                counts['partition_assignments'] += 1
            for h, members in unanchored.items():
                sizes = tuple(g.n for g in h)
                denominator = prod(factorial(size) for size in sizes)
                assert factorial(m) % denominator == 0
                placement_count = factorial(m) // denominator
                expected_placements = tuple(b for b in bs if tuple(map(len, b)) == sizes)
                assert len(expected_placements) == placement_count
                exponent = sum(sizes[i] * sizes[j] for i in range(k) for j in range(i + 1, k))
                generated = set()
                for b in expected_placements:
                    for cross in powerset(cross_pairs(m, b)):
                        generated.add((b, matrix_reconstruct(h, b, cross)))
                assert generated == members
                assert len(members) == placement_count * 2 ** exponent
                leaf_hist[len(members)] += 1
                counts['unanchored_fibres'] += 1
                counts['unanchored_members_checked'] += len(members)
            count = len(bs) * len(gs)
            row['partition_assignments'] += len(bs)
            row['graph_partition_pairs'] += count
            row['represented_typed_pairs'] += count * len(chain_strings(k))
        per_size.append(row)
    for key in ('graph_partition_pairs', 'represented_typed_pairs'):
        counts[key] = sum(row[key] for row in per_size)
    assert counts['partition_assignments'] == 1280
    assert counts['graph_partition_pairs'] == 64587
    assert counts['represented_typed_pairs'] == 1597940
    assert counts['unanchored_members_checked'] == counts['graph_partition_pairs']
    counts['ordered_graphs'] = sum(row['graphs'] for row in per_size)
    counts['physically_executed_graph_partition_pairs'] = counts['graph_partition_pairs']
    return {'counts': dict(counts), 'per_size': per_size,
            'anchored_fibre_size_histogram': dict(sorted(fibre_hist.items())),
            'unanchored_fibre_size_histogram': dict(sorted(leaf_hist.items())),
            'ordered_case_digest': case_hash.hexdigest()}


def arrows_check():
    rows = []
    for k in range(6):
        chains = chain_strings(k)
        assert len(chains) == (k + 3) * (k + 2) // 2
        for path in chains:
            arrows = tuple(zip(path, path[1:]))
            assert len(arrows) == k
            assert all(a <= b for a, b in arrows)
            assert all(arrows[j][1] == arrows[j + 1][0] for j in range(k - 1))
            if not arrows:
                composite = (path[0], path[0])
            else:
                composite = arrows[0]
                for a, b in arrows[1:]:
                    assert composite[1] == a
                    composite = (composite[0], b)
            assert composite == (path[0], path[-1])
        rows.append({'arity': k, 'physically_executed_strings': len(chains)})
    assert sum(x['physically_executed_strings'] for x in rows) == 83
    return {'category': 'three-object chain 0 <= 1 <= 2', 'per_arity': rows,
            'physically_executed_strings': 83,
            'factorization': 'Every graph/partition case pairs with every chain at its arity; graph maps inspect no arrows and arrow validity inspects no graph. No empty slot is deleted.'}


@dataclass(frozen=True)
class Comp:
    graph: Graph
    src: int
    dst: int

    def __post_init__(self):
        assert 0 <= self.src <= self.dst <= 2

    def code(self):
        return (self.graph.code(), self.src, self.dst)


@dataclass(frozen=True)
class Cut:
    whole: Comp
    blocks: tuple[tuple[int, ...], ...]
    path: tuple[int, ...]

    def __post_init__(self):
        valid_blocks(self.whole.graph.n, self.blocks)
        assert len(self.path) == len(self.blocks) + 1
        assert self.path[0] == self.whole.src and self.path[-1] == self.whole.dst
        assert all(0 <= a <= b <= 2 for a, b in zip(self.path, self.path[1:]))
        if not self.blocks:
            assert self.whole.graph.n == 0 and self.whole.src == self.whole.dst

    def profile(self):
        return tuple(Comp(self.whole.graph.restrict(b), self.path[i], self.path[i + 1])
                     for i, b in enumerate(self.blocks))

    def code(self):
        return (self.whole.code(), self.blocks, self.path)


def identity(c):
    return Cut(c, (tuple(range(c.graph.n)),), (c.src, c.dst))


def subst(cut, children):
    assert len(children) == len(cut.blocks)
    assert tuple(x.whole for x in children) == cut.profile()
    blocks = tuple(tuple(cut.blocks[i][x] for x in b)
                   for i, child in enumerate(children) for b in child.blocks)
    if not children:
        path = (cut.path[0],)
    else:
        path = (cut.path[0],) + tuple(v for child in children for v in child.path[1:])
    return Cut(cut.whole, blocks, path)


@dataclass(frozen=True)
class Tree:
    whole: Comp
    primitive: Cut | None = None
    children: tuple['Tree', ...] = ()

    def __post_init__(self):
        if self.primitive is None:
            assert not self.children
        else:
            assert self.whole == self.primitive.whole
            assert tuple(t.whole for t in self.children) == self.primitive.profile()
            assert len(self.children) in (0, 2)  # actual S_bin signature


def corolla(cut):
    return Tree(cut.whole, cut, tuple(Tree(c) for c in cut.profile()))


def evaluate(t):
    if t.primitive is None:
        return identity(t.whole)
    return subst(t.primitive, tuple(evaluate(c) for c in t.children))


def direct_evaluate(t):
    # Read ambient leaves along each address; no call to subst or evaluate.
    blocks, path_arrows = [], []
    def visit(s, embedding):
        assert len(embedding) == s.whole.graph.n
        assert t.whole.graph.restrict(embedding) == s.whole.graph
        if s.primitive is None:
            blocks.append(tuple(embedding))
            path_arrows.append((s.whole.src, s.whole.dst))
        else:
            for b, child in zip(s.primitive.blocks, s.children):
                visit(child, tuple(embedding[x] for x in b))
    visit(t, tuple(range(t.whole.graph.n)))
    path = (t.whole.src,) + tuple(b for a, b in path_arrows)
    assert all(path[i] == a for i, (a, _) in enumerate(path_arrows))
    return Cut(t.whole, tuple(blocks), path)


def shape(t):
    if t.primitive is None:
        return ('external-leaf',)
    return ('primitive-node', len(t.children), tuple(shape(c) for c in t.children))


def labels(t, address=()):
    if t.primitive is None:
        return ()
    return ((address, t.primitive),) + tuple(item for i, c in enumerate(t.children)
                                             for item in labels(c, address + (i,)))


def decode(whole, sh, label_pairs):
    lab = dict(label_pairs)
    assert len(lab) == len(label_pairs)
    used = set()
    def walk(c, s, a):
        if s == ('external-leaf',):
            assert a not in lab
            return Tree(c)
        assert s[0] == 'primitive-node' and s[1] == len(s[2])
        primitive = lab[a]
        used.add(a)
        assert primitive.whole == c and len(primitive.blocks) == s[1]
        children = tuple(walk(ci, si, a + (i,)) for i, (ci, si)
                         in enumerate(zip(primitive.profile(), s[2])))
        return Tree(c, primitive, children)
    answer = walk(whole, sh, ())
    assert used == set(lab)
    return answer


def build_grouping(g, blocks, path, grouping):
    def indices(s):
        return (s,) if isinstance(s, int) else indices(s[0]) + indices(s[1])
    def build(s):
        slots = indices(s)
        support = tuple(sorted(x for i in slots for x in blocks[i]))
        c = Comp(g.restrict(support), path[slots[0]], path[slots[-1] + 1])
        if isinstance(s, int):
            return Tree(c)
        parts = tuple(tuple(support.index(x) for x in sorted(y for i in indices(child) for y in blocks[i]))
                      for child in s)
        mid = path[indices(s[0])[-1] + 1]
        prim = Cut(c, parts, (c.src, mid, c.dst))
        return Tree(c, prim, tuple(build(child) for child in s))
    return build(grouping)


def json_graph(g):
    return {'vertices': g.n, 'edges': [list(x) for x in sorted(g.edges)]}


def six_vertex():
    blocks = ((0,), (1, 3), (2, 4), (5,))
    path = (0, 1, 1, 1, 2)
    g = Graph(6, frozenset(((0, 1), (1, 2), (1, 3), (2, 4), (3, 4), (4, 5))))
    h = leaves(g, blocks)
    x = cross_pairs(6, blocks)
    assert len(x) == 13
    family = set()
    family_digest = sha256()
    tree_checks = 0
    for cross in powerset(x):
        member = reconstruct(h, blocks, cross)
        assert matrix_reconstruct(h, blocks, cross) == member
        assert leaves(member, blocks) == h
        family.add(member)
        bal = build_grouping(member, blocks, path, ((0, 1), (2, 3)))
        right = build_grouping(member, blocks, path, (0, (1, (2, 3))))
        target = Cut(Comp(member, 0, 2), blocks, path)
        assert bal != right and shape(bal) != shape(right)
        assert evaluate(bal) == evaluate(right) == direct_evaluate(bal) == direct_evaluate(right) == target
        assert decode(bal.whole, shape(bal), labels(bal)) == bal
        assert decode(right.whole, shape(right), labels(right)) == right
        family_digest.update(repr(member.code()).encode())
        tree_checks += 2
    assert len(family) == 8192 and g in family
    cut = Cut(Comp(g, 0, 2), blocks, path)
    profile = cut.profile()
    assert profile[1] == profile[2] and profile[1].graph == Graph(2, frozenset({(0, 1)}))
    forward = Cut(profile[1], ((0,), (1,)), (1, 1, 1))
    reverse = Cut(profile[2], ((1,), (0,)), (1, 1, 1))
    assert forward != reverse and forward.profile() == reverse.profile()
    replacements = (identity(profile[0]), forward, reverse, identity(profile[3]))
    refined = subst(cut, replacements)
    assert refined.blocks == ((0,), (1,), (3,), (4,), (2,), (5,))
    assert refined.path == (0, 1, 1, 1, 1, 1, 2)
    plus = Graph(6, g.edges | {(0, 5)})
    assert g != plus and leaves(g, blocks) == leaves(plus, blocks)
    bal = build_grouping(g, blocks, path, ((0, 1), (2, 3)))
    right = build_grouping(g, blocks, path, (0, (1, (2, 3))))
    return {'family_members': len(family), 'cross_edge_bits': len(x),
            'recursive_tree_evaluations': tree_checks,
            'direct_tree_evaluations': tree_checks,
            'full_encoding_roundtrips': tree_checks,
            'family_ordered_digest': family_digest.hexdigest(),
            'base_graph': json_graph(g), 'blocks': blocks, 'interface_path': path,
            'repeated_components': [profile[1].code(), profile[2].code()],
            'middle_replacement_blocks': [forward.blocks, reverse.blocks],
            'refined_blocks': refined.blocks, 'refined_interface_path': refined.path,
            'all_family_groupings_equal_full_witness': True}, (cut, forward, reverse, replacements, refined, bal, right)


def obs(relation):
    return frozenset(x for x, _ in relation), frozenset(y for _, y in relation)


def truth(a, b, relation):
    return tuple((x, y) in relation for x in range(a) for y in range(b))


def relation_suite():
    matrices = supports = nonempty = 0
    histogram = defaultdict(int)
    per_domain = []
    for a in range(3):
        for b in range(4):
            relations = tuple(powerset(product(range(a), range(b))))
            groups = defaultdict(set)
            truths = set()
            for r in relations:
                groups[obs(r)].add(r)
                bits = truth(a, b, r)
                assert frozenset((x, y) for j, (x, y) in enumerate(product(range(a), range(b))) if bits[j]) == r
                truths.add(bits)
            assert len(truths) == len(relations)
            for d in powerset(range(a)):
                for ran in powerset(range(b)):
                    supports += 1
                    members = groups.get((d, ran), set())
                    expected = {r for r in powerset(product(sorted(d), sorted(ran))) if obs(r) == (d, ran)}
                    assert members == expected
                    exists = bool(d) == bool(ran)
                    assert bool(members) == exists
                    if exists:
                        nonempty += 1
                        singleton = not d or min(len(d), len(ran)) == 1
                        assert (len(members) == 1) == singleton
                        if d and ran and min(len(d), len(ran)) >= 2:
                            assert len(members) > 1
                    histogram[len(members)] += 1
            matrices += len(relations)
            per_domain.append({'a': a, 'b': b, 'matrices': len(relations), 'nonempty_support_fibres': len(groups)})
    assert (matrices, supports, nonempty) == (104, 105, 56)
    r = frozenset({(0, 0), (0, 1), (1, 2)})
    s = frozenset({(0, 0), (1, 1), (1, 2)})
    assert r != s and obs(r) == obs(s) and truth(2, 3, r) != truth(2, 3, s)
    return {'relation_matrices': matrices, 'support_candidates': supports,
            'nonempty_support_fibres': nonempty, 'support_fibre_histogram': dict(sorted(histogram.items())),
            'per_domain': per_domain, 'collision_2_by_3': {'R': sorted(r), 'S': sorted(s),
            'domain': sorted(obs(r)[0]), 'range': sorted(obs(r)[1])}}, (r, s)


def compose_rel(a, b):
    return frozenset((x, z) for x, y in a for yy, z in b if y == yy)


def rel_named():
    # Carrier labels A,B,C remain distinct; cardinalities 2,3,2.
    r = frozenset({(0, 0), (0, 1), (1, 2)})
    s = frozenset({(0, 0), (1, 0), (2, 1)})
    t = compose_rel(r, s)
    w = frozenset(product(range(2), repeat=2))
    assert t == frozenset({(0, 0), (1, 1)}) and t < w
    p = (('A', 'B', r), ('B', 'C', s))
    whole = ('A', 'C', w)
    primitive_assignment = {'alpha': (whole, p), 'beta': (whole, p)}
    def primitive_tree(symbol):
        c, q = primitive_assignment[symbol]
        return ('node', symbol, c, tuple(('leaf', child) for child in q))
    def evaluate_rel(tree):
        if tree[0] == 'leaf':
            c = tree[1]
            return c, (c,)
        _, symbol, c, children = tree
        assigned_c, assigned_p = primitive_assignment[symbol]
        assert c == assigned_c
        child_values = tuple(evaluate_rel(ch) for ch in children)
        assert tuple(value[0] for value in child_values) == assigned_p
        profile = tuple(component for _, child_profile in child_values for component in child_profile)
        assert all(profile[i][1] == profile[i + 1][0] for i in range(len(profile) - 1))
        composite = profile[0][2]
        for component in profile[1:]:
            composite = compose_rel(composite, component[2])
        assert composite <= c[2]
        return c, profile  # unique cell in this (whole, profile) fibre
    alpha, beta = primitive_tree('alpha'), primitive_tree('beta')
    assert alpha != beta and evaluate_rel(alpha) == evaluate_rel(beta) == (whole, p)
    exact_cell = (('A', 'C', t), p)
    nonexact_cell = evaluate_rel(alpha)
    assert exact_cell[1] == nonexact_cell[1] and exact_cell[0] != nonexact_cell[0]
    return {'carriers': {'A': 2, 'B': 3, 'C': 2}, 'R': sorted(r), 'S': sorted(s),
            'composite': sorted(t), 'whole': sorted(w),
            'strict_containment': True, 'distinct_symbols': ['alpha', 'beta'],
            'parallel_raw_trees_distinct': True, 'equal_full_semantic_cells': True,
            'same_profile_distinct_wholes': True,
            'warning': 'Cell equality is fixed-(profile,whole) thinness, not equality of raw symbols or realizing tuples.'}


def mutation_controls(six_data, observation_pair):
    cut, forward, reverse, replacements, refined, bal, right = six_data
    controls = []
    def record(name, changed_map, expected_distinct, actual_equal, evidence):
        assert expected_distinct and actual_equal, name
        controls.append({'name': name, 'executed_changed_map': changed_map,
                         'distinct_valid_inputs': True, 'mutated_outputs_equal': True,
                         'evidence': evidence})
    # Deliberately omit one real cross coordinate from storage, then reconstruct.
    g = cut.whole.graph
    plus = Graph(g.n, g.edges | {(0, 5)})
    cross = frozenset(plus.edges.intersection(cross_pairs(g.n, cut.blocks)))
    recovered_wrong = reconstruct(leaves(plus, cut.blocks), cut.blocks, cross - {(0, 5)})
    assert recovered_wrong != plus and recovered_wrong == g
    controls.append({'name': 'omit_cross_edge_in_reconstruction',
                     'executed_changed_map': 'cross -> cross minus {(0,5)} before reconstruct',
                     'failed_roundtrip': True, 'lost_edge': [0, 5],
                     'wrong_result_equals_other_valid_whole': recovered_wrong == g})
    # Two ordered singleton cuts have the same profile, full graph and cross set.
    f, r = forward, reverse
    repaired = lambda w: (w.profile(), w.blocks, w.whole.graph.edges.intersection(cross_pairs(w.whole.graph.n, w.blocks)))
    dropped = lambda w: (w.profile(), w.whole.graph.edges.intersection(cross_pairs(w.whole.graph.n, w.blocks)))
    assert repaired(f) != repaired(r)
    record('drop_ambient_block_placements', 'repair record drops B', f != r,
           dropped(f) == dropped(r), {'left_blocks': f.blocks, 'right_blocks': r.blocks})
    unordered = lambda w: (w.whole, tuple(sorted(w.blocks)), w.path)
    record('unordered_blocks', 'sort ordered blocks before equality', f != r,
           unordered(f) == unordered(r), {'left_blocks': f.blocks, 'right_blocks': r.blocks})
    # A real dictionary keyed by equal component values overwrites occurrence 1.
    by_colour = dict(zip(cut.profile(), replacements))
    deduplicated = tuple(by_colour[c] for c in cut.profile())
    wrong = subst(cut, deduplicated)
    assert wrong != refined
    controls.append({'name': 'deduplicate_equal_component_occurrences',
                     'executed_changed_map': 'dict(zip(profile,replacements)) then lookup by colour',
                     'failed_substitution_equality': True, 'expected_blocks': refined.blocks,
                     'mutated_blocks': wrong.blocks})
    ft, rt = corolla(f), corolla(r)
    assert shape(ft) == shape(rt) and labels(ft) != labels(rt)
    record('erase_primitive_labels', 'Enc drops address-to-primitive labels', ft != rt,
           (ft.whole, shape(ft)) == (rt.whole, shape(rt)), {'same_shape': shape(ft), 'opposite_blocks': [f.blocks, r.blocks]})
    record('claim_evaluation_injective', 'predicate equal Ev images implies equal trees', bal != right,
           evaluate(bal) == evaluate(right), {'left_shape': shape(bal), 'right_shape': shape(right)})
    a, b = observation_pair
    record('collapse_truth_to_support_observation', 'Truth matrix replaced by domain/range supports',
           a != b and truth(2, 3, a) != truth(2, 3, b), obs(a) == obs(b),
           {'R': sorted(a), 'S': sorted(b)})
    empty = Graph(0, frozenset())
    leaf = Tree(Comp(empty, 1, 1))
    nullary = Tree(leaf.whole, Cut(leaf.whole, (), (1,)), ())
    assert leaf != nullary and shape(leaf) != shape(nullary)
    assert evaluate(leaf).blocks == ((),) and evaluate(nullary).blocks == ()
    assert decode(leaf.whole, shape(leaf), labels(leaf)) == leaf
    assert decode(nullary.whole, shape(nullary), labels(nullary)) == nullary
    another_leaf = Tree(Comp(Graph(1, frozenset()), 1, 1))
    record('omit_root_from_empty_label_tree_encoding', 'Enc drops Out on identity trees', leaf != another_leaf,
           (shape(leaf), labels(leaf)) == (shape(another_leaf), labels(another_leaf)),
           {'root_vertex_counts': [0, 1]})
    return {'controls': controls, 'controls_executed': len(controls),
            'nullary_external_leaf_guard': {'same_root': True, 'shapes_distinct': True,
                                           'identity_blocks': evaluate(leaf).blocks, 'nullary_blocks': evaluate(nullary).blocks}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=HERE / 'AuthorCertificate.json')
    args = parser.parse_args()
    assert digest(ROOT / 'research/CompletionContract.md') == CONTRACT
    assert digest(HERE.parent / 'C3_Targets.md') == TARGET
    graph_result = graph_fibres()
    arrows_result = arrows_check()
    six_result, six_data = six_vertex()
    relation_result, obs_pair = relation_suite()
    named = rel_named()
    controls = mutation_controls(six_data, obs_pair)
    report = {'schema': 'C3-author-finite-v1', 'status': 'PASS',
              'contract_sha256': CONTRACT, 'target_sha256': TARGET,
              'source_sha256': digest(__file__),
              'evidence_level': 'C/X; not unrestricted P, Lean, or acceptance',
              'finite_domain': {'graph_sizes': list(range(5)), 'arities': list(range(6)),
                                'empty_blocks_retained': True, 'all_arities_claimed_finitely_exhaustive': False,
                                'relation_source_sizes': list(range(3)), 'relation_target_sizes': list(range(4))},
              'graphs': graph_result, 'interfaces': arrows_result,
              'six_vertex': six_result, 'relations': relation_result,
              'relational_signature': named, 'mutations': controls,
              'scope': 'C3 only. B2 accepted; C1/C2 local verified inputs, full C1/C2 gates remain OPEN. No later workstream activated.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'output': str(args.output),
                      'graph_partition_pairs': graph_result['counts']['graph_partition_pairs'],
                      'represented_typed_pairs': graph_result['counts']['represented_typed_pairs'],
                      'six_vertex_family': six_result['family_members'],
                      'relation_matrices': relation_result['relation_matrices'],
                      'negative_controls': controls['controls_executed']}, sort_keys=True))

if __name__ == '__main__':
    main()
