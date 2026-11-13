#!/usr/bin/env python3
"""Independent C3 C evidence; no imports from author or inherited model code.

Uses symmetric adjacency matrices and vertex-to-block label vectors. Frozen
domain: all m<=4, k<=5, all graphs and all [m]->[k]; all [2] arrow strings are
factored, not pretended physically run with each graph. Arbitrary arity belongs
to the separate P proof. C3-only, M-positive, contract v0.1, no acceptance claim.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations, product
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import sys

CONTRACT = '47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET = '88ea710752d99cd83d10c85740f825b1c543d58c0f475615c667020bc1aa2825'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def adjacency(m, bits):
    pairs = tuple(combinations(range(m), 2))
    selected = {p: b for p, b in zip(pairs, bits)}
    return tuple(tuple(0 if x == y else selected[tuple(sorted((x, y)))]
                       for y in range(m)) for x in range(m))


def all_graphs(m):
    return tuple(adjacency(m, b) for b in product((0, 1), repeat=comb(m, 2)))


def valid_graph(g):
    m = len(g)
    return (all(len(row) == m for row in g) and
            all(g[x][x] == 0 for x in range(m)) and
            all(g[x][y] in (0, 1) and g[x][y] == g[y][x]
                for x in range(m) for y in range(m)))


def leaf_graphs(g, labels, k):
    assert len(g) == len(labels)
    return tuple(tuple(tuple(g[x][y] for y in range(len(g)) if labels[y] == i)
                       for x in range(len(g)) if labels[x] == i)
                 for i in range(k))


def cross_pairs(labels):
    return tuple((x, y) for x in range(len(labels)) for y in range(x + 1, len(labels))
                 if labels[x] != labels[y])


def missing_data(g, labels):
    return tuple(g[x][y] for x, y in cross_pairs(labels))


def assemble(leaves, labels, cross):
    """Rebuild via local rank for internal entries, separately allocated cross bits."""
    m = len(labels)
    ranks = tuple(sum(labels[u] == labels[v] for u in range(v)) for v in range(m))
    bits = dict(zip(cross_pairs(labels), cross))
    assert len(bits) == len(cross_pairs(labels)) == len(cross)
    out = []
    for x in range(m):
        row = []
        for y in range(m):
            if labels[x] == labels[y]:
                row.append(leaves[labels[x]][ranks[x]][ranks[y]])
            else:
                row.append(bits[tuple(sorted((x, y)))])
        out.append(tuple(row))
    answer = tuple(out)
    assert valid_graph(answer)
    return answer


def chain_strings(k):
    return tuple(a for a in product(range(3), repeat=k + 1)
                 if all(a[j] <= a[j + 1] for j in range(k)))


def check_small_fibres():
    rows = []
    all_leaf_fibres = 0
    all_anchored_fibres = 0
    cross_coordinate_cases = 0
    chains = {k: chain_strings(k) for k in range(6)}
    for k, ss in chains.items():
        assert len(ss) == comb(k + 3, 2)
        for s in ss:
            arrows = tuple(zip(s, s[1:]))
            assert all(a[1] == b[0] for a, b in zip(arrows, arrows[1:]))
            composite = (s[0], s[0]) if not arrows else (arrows[0][0], arrows[-1][1])
            assert composite == (s[0], s[-1])
    for m in range(5):
        graphs = all_graphs(m)
        assert len(graphs) == 2 ** comb(m, 2)
        assignments = pairs = typed_pairs = anchored_fibres = total_fibres = 0
        for k in range(6):
            by_leaves = defaultdict(list)
            for labels in product(range(k), repeat=m):
                assignments += 1
                cross = cross_pairs(labels)
                ns = tuple(labels.count(i) for i in range(k))
                exponent = sum(ns[i] * ns[j] for i in range(k) for j in range(i + 1, k))
                assert len(cross) == exponent
                groups = defaultdict(set)
                for g in graphs:
                    pairs += 1
                    typed_pairs += len(chains[k])
                    h = leaf_graphs(g, labels, k)
                    groups[h].add(g)
                    by_leaves[h].append((g, labels))
                    c = missing_data(g, labels)
                    assert assemble(h, labels, c) == g
                    assert (len(cross) == 0) == (sum(n > 0 for n in ns) <= 1)
                for h, fibre in groups.items():
                    anchored_fibres += 1
                    expected = set()
                    for bits in product((0, 1), repeat=len(cross)):
                        rebuilt = assemble(h, labels, bits)
                        assert leaf_graphs(rebuilt, labels, k) == h
                        assert missing_data(rebuilt, labels) == bits
                        expected.add(rebuilt)
                        cross_coordinate_cases += 1
                    assert fibre == expected
                    assert len(fibre) == 2 ** exponent
            for h, fibre in by_leaves.items():
                total_fibres += 1
                sizes = tuple(len(x) for x in h)
                num_blocks = factorial(m)
                for n in sizes:
                    num_blocks //= factorial(n)
                exponent = sum(sizes[i] * sizes[j] for i in range(k) for j in range(i + 1, k))
                assert len(set(fibre)) == len(fibre) == num_blocks * 2 ** exponent
                partitions = {labels for _, labels in fibre}
                assert len(partitions) == num_blocks
                for labels in partitions:
                    these = {missing_data(g, labels) for g, p in fibre if p == labels}
                    assert these == set(product((0, 1), repeat=exponent))
        all_anchored_fibres += anchored_fibres
        all_leaf_fibres += total_fibres
        rows.append({'vertices': m, 'graphs': len(graphs), 'partitions': assignments,
                     'graph_partition_pairs': pairs, 'represented_typed_pairs': typed_pairs,
                     'anchored_fibres': anchored_fibres, 'unanchored_leaf_fibres': total_fibres})
    assert sum(r['partitions'] for r in rows) == 1280
    assert sum(r['graph_partition_pairs'] for r in rows) == 64587
    assert sum(r['represented_typed_pairs'] for r in rows) == 1597940
    return {'rows': rows, 'partition_assignments': 1280, 'graph_partition_pairs': 64587,
            'represented_typed_pairs': 1597940, 'arrow_strings_physically_checked': sum(map(len, chains.values())),
            'anchored_fibres': all_anchored_fibres, 'unanchored_leaf_fibres': all_leaf_fibres,
            'cross_coordinate_inverse_cases': cross_coordinate_cases}


@dataclass(frozen=True)
class Component:
    matrix: tuple
    source: int
    target: int


@dataclass(frozen=True)
class Cut:
    matrix: tuple
    chain: tuple
    labels: tuple

    @property
    def arity(self):
        return len(self.chain) - 1

    @property
    def whole(self):
        return Component(self.matrix, self.chain[0], self.chain[-1])

    @property
    def leaves(self):
        return tuple(Component(g, self.chain[i], self.chain[i + 1])
                     for i, g in enumerate(leaf_graphs(self.matrix, self.labels, self.arity)))

    def check(self):
        assert valid_graph(self.matrix)
        assert len(self.chain) >= 1 and all(a <= b for a, b in zip(self.chain, self.chain[1:]))
        assert len(self.matrix) == len(self.labels)
        assert all(0 <= a < self.arity for a in self.labels)
        if self.arity == 0:
            assert self.matrix == () and self.chain[0] == self.chain[-1]
        return self


def identity(c):
    return Cut(c.matrix, (c.source, c.target), (0,) * len(c.matrix)).check()


def substitute(outer, replacements):
    outer.check()
    assert len(replacements) == outer.arity
    offsets = []
    chain = [outer.chain[0]]
    arity = 0
    for c, inner in zip(outer.leaves, replacements):
        inner.check()
        assert inner.whole == c
        offsets.append(arity)
        arity += inner.arity
        assert chain[-1] == inner.chain[0]
        chain.extend(inner.chain[1:])
    labels = []
    for v, i in enumerate(outer.labels):
        local_rank = sum(j == i for j in outer.labels[:v])
        labels.append(offsets[i] + replacements[i].labels[local_rank])
    answer = Cut(outer.matrix, tuple(chain), tuple(labels)).check()
    assert answer.leaves == tuple(c for inner in replacements for c in inner.leaves)
    return answer


@dataclass(frozen=True)
class Tree:
    whole: Component
    primitive: Cut | None
    children: tuple

    def evaluate(self):
        if self.primitive is None:
            assert not self.children
            return identity(self.whole)
        self.primitive.check()
        assert self.primitive.whole == self.whole
        assert tuple(c.whole for c in self.children) == self.primitive.leaves
        return substitute(self.primitive, tuple(c.evaluate() for c in self.children))

    def frontier(self):
        if self.primitive is None:
            return (self.whole,)
        return tuple(c for child in self.children for c in child.frontier())

    def shape(self):
        return ('leaf',) if self.primitive is None else ('node', tuple(c.shape() for c in self.children))

    def labels(self, address=()):
        if self.primitive is None:
            return ()
        return ((address, self.primitive),) + tuple(q for i, c in enumerate(self.children)
                                                  for q in c.labels(address + (i,)))

    def encoding(self):
        return self.whole, self.shape(), self.labels()


def restore_tree(whole, shape, label_entries):
    label_map = dict(label_entries)
    visited = set()
    def visit(c, s, address):
        if s == ('leaf',):
            assert address not in label_map
            return Tree(c, None, ())
        assert s[0] == 'node'
        primitive = label_map[address]
        visited.add(address)
        assert primitive.whole == c and primitive.arity == len(s[1])
        return Tree(c, primitive, tuple(visit(d, child_shape, address + (i,))
                    for i, (d, child_shape) in enumerate(zip(primitive.leaves, s[1]))))
    t = visit(whole, shape, ())
    assert visited == set(label_map)
    return t


def grouping_tree(g, block_vertices, chain, shape):
    """Construct all local primitive data from ambient supports, not flat evaluation."""
    def descendant_indices(s):
        return (s,) if isinstance(s, int) else descendant_indices(s[0]) + descendant_indices(s[1])

    def build(s):
        ix = descendant_indices(s)
        assert ix == tuple(range(min(ix), max(ix) + 1))
        support = tuple(sorted(v for i in ix for v in block_vertices[i]))
        local_graph = tuple(tuple(g[x][y] for y in support) for x in support)
        whole = Component(local_graph, chain[min(ix)], chain[max(ix) + 1])
        if isinstance(s, int):
            return Tree(whole, None, ())
        left_ix = descendant_indices(s[0])
        left_vertices = {v for i in left_ix for v in block_vertices[i]}
        labels = tuple(0 if v in left_vertices else 1 for v in support)
        middle = chain[max(left_ix) + 1]
        primitive = Cut(local_graph, (whole.source, middle, whole.target), labels).check()
        return Tree(whole, primitive, (build(s[0]), build(s[1])))
    return build(shape)


def graph_from_edges(m, edges):
    return tuple(tuple(int((min(x, y), max(x, y)) in edges) if x != y else 0
                       for y in range(m)) for x in range(m))


def blocks_of(cut):
    return tuple(tuple(v for v, i in enumerate(cut.labels) if i == j) for j in range(cut.arity))


def check_six_and_separations():
    g = graph_from_edges(6, {(0, 1), (1, 2), (1, 3), (2, 4), (3, 4), (4, 5)})
    labels = (0, 1, 2, 1, 2, 3)
    chain = (0, 1, 1, 1, 2)
    w = Cut(g, chain, labels).check()
    assert w.leaves[1] == w.leaves[2]
    assert len(w.leaves[1].matrix) == 2 and w.leaves[1].matrix[0][1] == 1
    forward = Cut(w.leaves[1].matrix, (1, 1, 1), (0, 1)).check()
    reverse = Cut(w.leaves[2].matrix, (1, 1, 1), (1, 0)).check()
    assert forward.whole == reverse.whole and forward.leaves == reverse.leaves and forward != reverse
    reps = (identity(w.leaves[0]), forward, reverse, identity(w.leaves[3]))
    refined = substitute(w, reps)
    expected_blocks = ((0,), (1,), (3,), (4,), (2,), (5,))
    assert blocks_of(refined) == expected_blocks
    assert refined.matrix == g
    b = blocks_of(w)
    bal = grouping_tree(g, b, chain, ((0, 1), (2, 3)))
    right = grouping_tree(g, b, chain, (0, (1, (2, 3))))
    assert bal != right and bal.shape() != right.shape()
    assert bal.frontier() == right.frontier() == w.leaves
    assert bal.evaluate() == right.evaluate() == w
    h = tuple(c.matrix for c in w.leaves)
    crossing = cross_pairs(labels)
    assert len(crossing) == 13
    worlds = set()
    family_trees = 0
    for bits in product((0, 1), repeat=13):
        rebuilt = assemble(h, labels, bits)
        candidate = Cut(rebuilt, chain, labels).check()
        assert candidate.leaves == w.leaves
        assert missing_data(rebuilt, labels) == bits
        assert leaf_graphs(rebuilt, labels, 4) == h
        for shape in (((0, 1), (2, 3)), (0, (1, (2, 3)))):
            tree = grouping_tree(rebuilt, b, chain, shape)
            assert tree.evaluate() == candidate
            assert tree.frontier() == candidate.leaves
            assert restore_tree(*tree.encoding()) == tree
            family_trees += 1
        worlds.add(rebuilt)
    assert len(worlds) == 8192

    # Actual counterfactual maps, each falsified using valid source objects.
    controls = {}
    first_cross = crossing[0]
    empty_bits = (0,) * 13
    one_bits = (1,) + (0,) * 12
    g0 = assemble(h, labels, empty_bits)
    g1 = assemble(h, labels, one_bits)
    assert g0 != g1
    def corrupt_rebuild(leaves, labs, bits):
        return assemble(leaves, labs, (0,) + bits[1:])
    assert corrupt_rebuild(h, labels, one_bits) != g1
    controls['omit_cross_coordinate'] = {'detected': True, 'coordinate': list(first_cross)}
    assert (h, labels) == (leaf_graphs(g1, labels, 4), labels)
    controls['forget_all_cross_data'] = {'detected': True}

    # An edgeless six-vertex repair pair drops B but keeps the SAME cross set.
    edgeless = graph_from_edges(6, set())
    lab2 = (0, 2, 1, 2, 1, 3)
    e0, e1 = Cut(edgeless, chain, labels), Cut(edgeless, chain, lab2)
    def repaired(c):
        return c.leaves, c.labels, frozenset(p for p in cross_pairs(c.labels) if c.matrix[p[0]][p[1]])
    def drop_partition(c):
        p, _, e = repaired(c)
        return p, e
    assert repaired(e0) != repaired(e1) and drop_partition(e0) == drop_partition(e1)
    controls['drop_partition_from_repair'] = {'detected': True}

    def unordered_cut(c):
        return c.whole, tuple(sorted(blocks_of(c))), c.chain
    assert unordered_cut(forward) == unordered_cut(reverse)
    controls['unordered_blocks'] = {'detected': True}
    table = {component: replacement for component, replacement in zip(w.leaves, reps)}
    merged = substitute(w, tuple(table[c] for c in w.leaves))
    assert merged != refined and blocks_of(merged) != expected_blocks
    controls['deduplicate_occurrences'] = {'detected': True, 'wrong_blocks': blocks_of(merged)}
    def corolla(c):
        return Tree(c.whole, c, tuple(Tree(x, None, ()) for x in c.leaves))
    t0, t1 = corolla(forward), corolla(reverse)
    assert t0 != t1 and t0.whole == t1.whole and t0.shape() == t1.shape()
    assert t0.labels() != t1.labels() and t0.encoding() != t1.encoding()
    controls['erase_primitive_labels'] = {'detected': (t0.whole, t0.shape()) == (t1.whole, t1.shape())}
    def claimed_injective(presentations, projection):
        return len({projection(t) for t in presentations}) == len(set(presentations))
    assert not claimed_injective((bal, right), lambda t: t.evaluate())
    controls['claim_Ev_injective'] = {'detected': True}
    cempty = Component((), 1, 1)
    tid = Tree(cempty, None, ())
    tnull = Tree(cempty, Cut((), (1,), ()), ())
    assert tid.shape() != tnull.shape() and tid.evaluate() != tnull.evaluate()
    t_other_id = Tree(Component((), 0, 0), None, ())
    assert tid.shape() == t_other_id.shape() and tid.labels() == t_other_id.labels()
    assert tid.encoding() != t_other_id.encoding()
    examples = (bal, right, t0, t1, tid, tnull, t_other_id)
    assert claimed_injective(examples, lambda t: t.encoding())
    return {'cross_bits': 13, 'cross_family_graphs': len(worlds), 'whole_vertices': 6,
            'recursive_family_tree_evaluations': family_trees,
            'family_encoding_roundtrips': family_trees,
            'middle_components_equal_nonempty': True, 'middle_local_cuts_distinct': True,
            'whole_profile_same_cut_distinct': True, 'same_frontier_distinct_trees': True,
            'same_evaluation_distinct_trees': True, 'refined_blocks': expected_blocks,
            'encoded_named_trees': len(examples), 'controls': controls}


def relation(a, b, bits):
    return tuple(tuple(bits[x * b + y] for y in range(b)) for x in range(a))


def supports(mat, b):
    return (tuple(x for x, row in enumerate(mat) if any(row)),
            tuple(y for y in range(b) if any(mat[x][y] for x in range(len(mat)))))


def rel_comp(r, s, a, b, c):
    return tuple(tuple(int(any(r[x][y] and s[y][z] for y in range(b)))
                       for z in range(c)) for x in range(a))


def check_relations():
    matrices = candidates = inhabited = 0
    rows = []
    for a in range(3):
        for b in range(4):
            groups = defaultdict(set)
            domain_matrices = []
            for bits in product((0, 1), repeat=a * b):
                mat = relation(a, b, bits)
                groups[supports(mat, b)].add(mat)
                domain_matrices.append(mat)
                matrices += 1
            assert len(domain_matrices) == len(set(domain_matrices)) == 2 ** (a * b)
            local_inhabited = 0
            for d_bits in product((0, 1), repeat=a):
                d = tuple(x for x in range(a) if d_bits[x])
                for r_bits in product((0, 1), repeat=b):
                    rr = tuple(y for y in range(b) if r_bits[y])
                    candidates += 1
                    fibre = groups.get((d, rr), set())
                    if bool(d) != bool(rr):
                        assert not fibre
                        continue
                    expected = set()
                    for local_bits in product((0, 1), repeat=len(d) * len(rr)):
                        values = {(x, y): local_bits[i * len(rr) + j]
                                  for i, x in enumerate(d) for j, y in enumerate(rr)}
                        if not all(any(values[x, y] for y in rr) for x in d):
                            continue
                        if not all(any(values[x, y] for x in d) for y in rr):
                            continue
                        expected.add(tuple(tuple(values.get((x, y), 0) for y in range(b)) for x in range(a)))
                    assert fibre == expected and fibre
                    inhabited += 1
                    local_inhabited += 1
                    if not d or min(len(d), len(rr)) == 1:
                        assert len(fibre) == 1
                    else:
                        assert len(fibre) > 1
            rows.append({'a': a, 'b': b, 'relations': len(domain_matrices), 'support_fibres': local_inhabited})
    assert (matrices, candidates, inhabited) == (104, 105, 56)
    obs0 = ((1, 1, 0), (0, 0, 1))
    obs1 = ((1, 0, 0), (0, 1, 1))
    assert obs0 != obs1 and supports(obs0, 3) == supports(obs1, 3) == ((0, 1), (0, 1, 2))
    assert len({obs0, obs1}) == 2 and len({supports(x, 3) for x in (obs0, obs1)}) == 1

    # Three genuinely distinct interface labels with sizes 2,3,2; B is unequal.
    sizes = {'A': 2, 'B': 3, 'C': 2}
    r = ((1, 1, 0), (0, 0, 1))
    s = ((1, 0), (1, 0), (0, 1))
    composite = rel_comp(r, s, 2, 3, 2)
    assert composite == ((1, 0), (0, 1))
    whole = ((1, 1), (1, 1))
    assert composite != whole and all(not composite[x][z] or whole[x][z] for x in range(2) for z in range(2))
    profile = (('A', 'B', r), ('B', 'C', s))
    w = ('A', 'C', whole)
    primitives = (('alpha', profile, w), ('beta', profile, w))
    def eval_primitive(symbol):
        _, p, target = symbol
        assert p[0][1] == p[1][0]
        calculated = rel_comp(p[0][2], p[1][2], sizes[p[0][0]], sizes[p[0][1]], sizes[p[1][1]])
        assert all(not calculated[x][z] or target[2][x][z] for x in range(len(calculated))
                   for z in range(len(calculated[0])))
        return p, target, 'the unique containment cell'
    assert primitives[0] != primitives[1]
    assert eval_primitive(primitives[0]) == eval_primitive(primitives[1])
    exact_symbol = ('gamma', profile, ('A', 'C', composite))
    assert eval_primitive(exact_symbol) != eval_primitive(primitives[0])
    return {'rows': rows, 'matrices': matrices, 'support_candidates': candidates,
            'inhabited_support_fibres': inhabited, 'observation_pair': [obs0, obs1],
            'truth_injective_observation_not': True,
            'primitive_certificate': {'interfaces': sizes, 'R': r, 'S': s,
                                      'composite': composite, 'strict_whole': whole,
                                      'distinct_symbols_equal_semantic_cells': True,
                                      'same_profile_distinct_wholes_stay_distinct': True},
            'controls': {'Truth_to_Obs': {'detected': True}}}


def verify_inputs(root):
    if root is None:
        return {'mode': 'standalone finite implementation, no project files required'}
    root = Path(root)
    target = root / 'research/workstream_C3/C3_Targets.md'
    contract = root / 'research/CompletionContract.md'
    assert digest(contract) == CONTRACT and digest(target) == TARGET
    baseline = json.loads((root / 'research/workstream_C3/BaselinePreservation.json').read_text())
    assert baseline['count'] == len(baseline['files']) == 578
    for f in baseline['files']:
        assert digest(root / f['path']) == f['sha256'], f['path']
    return {'mode': 'project input and 578-file baseline verification', 'baseline_files_unchanged': 578,
            'contract_sha256': CONTRACT, 'target_sha256': TARGET}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    parser.add_argument('--root')
    args = parser.parse_args()
    result = {'schema': 'C3-independent-finite-v1', 'status': 'RUNNING',
              'contract_sha256': CONTRACT, 'target_sha256': TARGET,
              'source_sha256': digest(__file__), 'python': sys.version.split()[0],
              'evidence_level': 'C; not all-size P or Lean L, no acceptance claim',
              'scope': 'C3 only; finite m<=4 k<=5; all-arity proof is separate',
              'inputs': verify_inputs(args.root)}
    result['small_graphs'] = check_small_fibres()
    result['six_vertex_and_syntax'] = check_six_and_separations()
    result['relations'] = check_relations()
    result['status'] = 'PASS'
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': result['status'], 'output': str(args.output),
                      'small_graphs': result['small_graphs'],
                      'six_vertex_graphs': result['six_vertex_and_syntax']['cross_family_graphs'],
                      'relations': result['relations']['matrices']}, indent=2))


if __name__ == '__main__':
    main()
