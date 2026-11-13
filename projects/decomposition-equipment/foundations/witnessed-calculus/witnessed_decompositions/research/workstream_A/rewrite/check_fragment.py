#!/usr/bin/env python3
"""Finite support for THEOREM.md, not a proof of its unbounded theorem.

Only Python's standard library is used. K is [2] x C2, with nonidentity
loops, and M is Z/3. The actual rewrite engine retains whole graphs and
cut inclusions; its normalizer does not merely flatten unlabelled trees.
"""
from dataclasses import dataclass, replace
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import hashlib
import json
import time


@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple

    def restrict(self, vertices):
        vs = tuple(sorted(vertices))
        edges = set(self.edges)
        return Graph(len(vs), tuple((i, j) for i in range(len(vs))
                                  for j in range(i + 1, len(vs))
                                  if (vs[i], vs[j]) in edges))


@dataclass(frozen=True)
class Arrow:
    a: int
    b: int
    grade: int = 0

    def then(self, other):
        assert self.b == other.a
        return Arrow(self.a, other.b, (self.grade + other.grade) % 2)


@dataclass(frozen=True)
class Term:
    kind: str
    graph: Graph
    arrow: Arrow
    children: tuple = ()
    left: tuple = ()
    value: int = 0


def leaf(g, f):
    return Term('L', g, f)


def unit(a):
    return Term('U', Graph(0, ()), Arrow(a, a))


def deco(m, x):
    return Term('D', x.graph, x.arrow, (x,), value=m)


def cut(g, left, x, y):
    left = tuple(sorted(left))
    right = tuple(i for i in range(g.n) if i not in left)
    assert len(set(left)) == len(left)
    assert x.graph == g.restrict(left)
    assert y.graph == g.restrict(right)
    return Term('C', g, x.arrow.then(y.arrow), (x, y), left)


@lru_cache(None)
def evaluation(t):
    """Recursive flat substitution evaluation."""
    if t.kind == 'L':
        return (t.graph, (tuple(range(t.graph.n)),), (t.arrow,), 0)
    if t.kind == 'U':
        return (t.graph, (), (), 0)
    if t.kind == 'D':
        g, bs, fs, m = evaluation(t.children[0])
        return (g, bs, fs, (m + t.value) % 3)
    x, y = t.children
    _, bx, fx, mx = evaluation(x)
    _, by, fy, my = evaluation(y)
    right = tuple(i for i in range(t.graph.n) if i not in t.left)
    blocks = tuple(tuple(t.left[i] for i in b) for b in bx)
    blocks += tuple(tuple(right[i] for i in b) for b in by)
    return (t.graph, blocks, fx + fy, (mx + my) % 3)


def address_evaluation(t):
    """Separate traversal: carry inclusions to the root; collect leaves."""
    blocks, arrows, values = [], [], []

    def walk(q, embedding):
        if q.kind == 'L':
            blocks.append(tuple(embedding))
            arrows.append(q.arrow)
        elif q.kind == 'D':
            values.append(q.value)
            walk(q.children[0], embedding)
        elif q.kind == 'C':
            left = set(q.left)
            walk(q.children[0], tuple(embedding[i] for i in q.left))
            walk(q.children[1], tuple(embedding[i] for i in range(q.graph.n)
                                      if i not in left))
    walk(t, tuple(range(t.graph.n)))
    return (t.graph, tuple(blocks), tuple(arrows), sum(values) % 3)


def compose(fs, base):
    out = Arrow(base, base)
    for f in fs:
        out = out.then(f)
    return out


def canonical(w, base):
    g, bs, fs, m = w
    if not bs:
        assert g.n == 0 and not fs
        out = unit(base)
    elif len(bs) == 1:
        assert bs[0] == tuple(range(g.n))
        out = leaf(g, fs[0])
    else:
        tail = tuple(sorted(v for b in bs[1:] for v in b))
        positions = {v: i for i, v in enumerate(tail)}
        tail_blocks = tuple(tuple(positions[v] for v in b) for b in bs[1:])
        y = canonical((g.restrict(tail), tail_blocks, fs[1:], 0), fs[0].b)
        out = cut(g, bs[0], leaf(g.restrict(bs[0]), fs[0]), y)
    return out if m == 0 else deco(m, out)


@lru_cache(None)
def measure(t):
    if t.kind in ('L', 'U'):
        return (0, 0, 0, 0)
    if t.kind == 'D':
        b, a, h, d = measure(t.children[0])
        return (b, a, h, d + 1)
    bx, ax, hx, dx = measure(t.children[0])
    by, ay, hy, dy = measure(t.children[1])
    return (1 + bx + by, ax + ay + bx, hx + hy + dx + dy, dx + dy)


def root_steps(t, omit=frozenset()):
    out = []
    if t.kind == 'D':
        x = t.children[0]
        if t.value == 0 and 'D0' not in omit:
            out.append(('D0', x))
        if x.kind == 'D' and 'DA' not in omit:
            out.append(('DA', deco((t.value + x.value) % 3, x.children[0])))
    if t.kind == 'C':
        x, y = t.children
        if x.kind == 'U' and 'UL' not in omit:
            out.append(('UL', y))
        if y.kind == 'U' and 'UR' not in omit:
            out.append(('UR', x))
        if x.kind == 'D' and 'DL' not in omit:
            out.append(('DL', deco(x.value, cut(t.graph, t.left, x.children[0], y))))
        if y.kind == 'D' and 'DR' not in omit:
            out.append(('DR', deco(y.value, cut(t.graph, t.left, x, y.children[0]))))
        if x.kind == 'C' and 'R' not in omit:
            xx, xy = x.children
            u = tuple(t.left[i] for i in x.left)
            v = tuple(t.left[i] for i in range(x.graph.n) if i not in x.left)
            vw = tuple(i for i in range(t.graph.n) if i not in u)
            locv = tuple(vw.index(i) for i in v)
            inner = cut(t.graph.restrict(vw), locv, xy, y)
            out.append(('R', cut(t.graph, u, xx, inner)))
    return out


def steps(t, omit=frozenset()):
    out = root_steps(t, omit)
    for i, child in enumerate(t.children):
        for label, q in steps(child, omit):
            children = list(t.children)
            children[i] = q
            out.append((f'{i}/{label}', replace(t, children=tuple(children))))
    return out


def normalize(t, omit=frozenset()):
    count = 0
    while True:
        options = steps(t, omit)
        if not options:
            return t, count
        q = options[0][1]
        assert measure(q) < measure(t)
        t = q
        count += 1


def C(x, y):
    return ('C', x, y)


def D(m, x):
    return ('D', m, x)


PATTERNS = [
    C(C('x', 'y'), 'u'), C(C('x', 'y'), D('m', 'z')),
    C('u', 'u'), C('u', D('m', 'x')), C(D('m', 'x'), 'u'),
    C(D('m', 'x'), D('n', 'y')), D(0, D('n', 'x')),
    C(C(C('x', 'y'), 'z'), 'w'), C(C('u', 'x'), 'y'),
    C(C('x', 'u'), 'y'), C(C(D('m', 'x'), 'y'), 'z'),
    C(C('x', D('m', 'y')), 'z'), D('m', D('n', D('p', 'x'))),
    D('m', D(0, 'x')), C(D('m', D('n', 'x')), 'y'),
    C(D(0, 'x'), 'y'), C('x', D('m', D('n', 'y'))), C('x', D(0, 'y')),
]


def symbols(pattern):
    if isinstance(pattern, str):
        return ([] if pattern == 'u' else [pattern], set())
    if pattern[0] == 'D':
        ls, ds = symbols(pattern[2])
        return ls, ds | ({pattern[1]} if isinstance(pattern[1], str) else set())
    la, da = symbols(pattern[1])
    lb, db = symbols(pattern[2])
    return la + lb, da | db


def realize(pattern, g, blocks, fs, objects, vals):
    cursor = 0

    def walk(p):
        nonlocal cursor
        if p == 'u':
            return unit(objects[cursor]), ()
        if isinstance(p, str):
            vertices = blocks[cursor]
            q = leaf(g.restrict(vertices), fs[cursor])
            cursor += 1
            return q, vertices
        if p[0] == 'D':
            q, vs = walk(p[2])
            return deco(vals[p[1]] if isinstance(p[1], str) else p[1], q), vs
        x, vx = walk(p[1])
        y, vy = walk(p[2])
        vs = tuple(sorted(vx + vy))
        return cut(g.restrict(vs), tuple(vs.index(v) for v in vx), x, y), vs
    t, vs = walk(pattern)
    assert cursor == len(blocks) and vs == tuple(range(g.n))
    return t


def graphs(max_n):
    for n in range(max_n + 1):
        pairs = list(combinations(range(n), 2))
        for bits in product((0, 1), repeat=len(pairs)):
            yield Graph(n, tuple(p for p, bit in zip(pairs, bits) if bit))


def check_term(t):
    w = evaluation(t)
    assert address_evaluation(t) == w
    nf = canonical(w, t.arrow.a)
    assert evaluation(nf) == w
    assert not steps(nf)
    reducts = steps(t)
    for _, q in reducts:
        assert q.graph == t.graph and q.arrow == t.arrow
        assert evaluation(q) == w
        assert measure(q) < measure(t)
        actual, _ = normalize(q)
        assert actual == nf
    actual, _ = normalize(t)
    assert actual == nf
    return len(reducts)


def run():
    start = time.monotonic()
    per_shape, total_steps = [], 0
    for number, pattern in enumerate(PATTERNS, 1):
        leaves, labels = symbols(pattern)
        k = len(leaves)
        labels = sorted(labels)
        count = 0
        for g in graphs(2):
            if k == 0 and g.n:
                continue
            for assignment in product(range(k), repeat=g.n):
                blocks = tuple(tuple(v for v, b in enumerate(assignment) if b == i)
                               for i in range(k))
                for objects in combinations_with_replacement(range(3), k + 1):
                    for grades in product(range(2), repeat=k):
                        fs = tuple(Arrow(objects[i], objects[i + 1], grades[i])
                                   for i in range(k))
                        for values in product(range(3), repeat=len(labels)):
                            t = realize(pattern, g, blocks, fs, objects,
                                        dict(zip(labels, values)))
                            total_steps += check_term(t)
                            count += 1
        per_shape.append({'row': number, 'instantiations': count})
        evaluation.cache_clear()
        measure.cache_clear()

    # Six-vertex principal certificate with repeated nonempty components.
    g = Graph(6, ((0, 5), (1, 2), (2, 3), (3, 4)))
    bs = ((0,), (1, 2), (3, 4), (5,))
    objects = (0, 1, 1, 1, 2)
    fs = tuple(Arrow(objects[i], objects[i + 1]) for i in range(4))
    mixed = C(C(C('a', D(1, 'b')), D(2, 'c')), 'd')
    t = realize(mixed, g, bs, fs, objects, {})
    total_steps += check_term(t)
    expected = canonical((g, bs, fs, 0), 0)
    assert normalize(t)[0] == expected
    assert g.restrict(bs[1]) == g.restrict(bs[2])
    assert fs[1] == fs[2]

    # A decoration on an actual unit is preserved, but an empty identity leaf
    # is a separate external occurrence and cannot be erased.
    x = leaf(Graph(1, ()), Arrow(0, 1))
    udecor = cut(x.graph, (), deco(1, unit(0)), x)
    assert normalize(udecor)[0] == deco(1, x)
    empty_leaf = cut(x.graph, (), leaf(Graph(0, ()), Arrow(0, 0)), x)
    assert normalize(empty_leaf)[0] == empty_leaf
    assert len(evaluation(empty_leaf)[1]) == 2
    nonidentity_empty = leaf(Graph(0, ()), Arrow(0, 0, 1))
    blocked_unit = cut(x.graph, (), nonidentity_empty, x)
    assert normalize(blocked_unit)[0] == blocked_unit

    # Same input graphs and arrow profile, different actual partitions.
    edgeless = Graph(2, ())
    af = (Arrow(0, 1), Arrow(1, 2))
    wa = (edgeless, ((0,), (1,)), af, 0)
    wb = (edgeless, ((1,), (0,)), af, 0)
    assert canonical(wa, 0) != canonical(wb, 0)
    assert evaluation(canonical(wa, 0)) != evaluation(canonical(wb, 0))
    # Same partition and induced pieces, different whole cross edge.
    edge = Graph(2, ((0, 1),))
    assert edge.restrict((0,)) == edgeless.restrict((0,))
    assert canonical((edge, wa[1], af, 0), 0) != canonical(wa, 0)

    # Mutation: deleting DL leaves two irreducible outcomes of row 12.
    g3 = Graph(3, ((0, 2),))
    bs3 = ((0,), (1,), (2,))
    o3 = (0, 1, 1, 2)
    f3 = tuple(Arrow(o3[i], o3[i + 1]) for i in range(3))
    bad = realize(PATTERNS[11], g3, bs3, f3, o3, {'m': 1})
    choices = steps(bad, frozenset({'DL'}))
    endpoints = {normalize(q, frozenset({'DL'}))[0] for _, q in choices}
    assert len(endpoints) == 2
    # Nontermination: adding inverse rotation produces a literal 2-cycle.
    rot = realize(C(C('x', 'y'), 'z'), g3, bs3, f3, o3, {})
    rotated = next(q for rule, q in root_steps(rot) if rule == 'R')
    assert measure(rotated) < measure(rot)
    inverse_cycle = (rot, rotated, rot)
    assert inverse_cycle[0] == inverse_cycle[2] != inverse_cycle[1]
    # Finite noncommutative monoid: constant transformations on two points.
    compose_transform = lambda a, b: tuple(a[b[i]] for i in range(2))
    m, n = (0, 0), (1, 1)
    assert compose_transform(m, n) == m
    assert compose_transform(n, m) == n

    return {
        'status': 'PASS',
        'evidence_kind': 'C, author-run finite regression evidence, not L or a general proof',
        'domain': {
            'all_ordered_simple_graphs_up_to_vertices': 2,
            'graphs': 4,
            'critical_shape_rows': 18,
            'partitions': 'all ordered assignments to metavariable leaves, including empty blocks',
            'interfaces': '[2] x C2: 3 objects, 12 arrows, including nonidentity loops',
            'arrow_strings': 'all composable strings for each critical shape',
            'monoid': 'Z/3, all values at all decoration metavariables',
            'metavariables': 'identity leaves; arbitrary substituted terms are covered by the P proof, not this finite run',
        },
        'critical_instantiations': sum(x['instantiations'] for x in per_shape),
        'one_step_reducts_checked': total_steps,
        'per_shape': per_shape,
        'additional_certificates': ['six-vertex repeated nonempty components',
            'decoration-bearing nullary', 'empty identity leaf retained',
            'nonidentity-loop empty leaf retained', 'partition inclusion separation',
            'cross-edge whole separation'],
        'negative_controls': {'missing_DL_nonconfluence': 'detected two normal forms',
            'reverse_rotation_nontermination': 'explicit 2-cycle',
            'noncommutative_transformation_monoid': 'unequal mn and nm'},
        'redundancy': 'recursive flat evaluation compared with separate root-address traversal; same author, not independent authorship',
        'elapsed_seconds': round(time.monotonic() - start, 3),
        'python_source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == '__main__':
    report = run()
    path = Path(__file__).with_name('CHECKS.json')
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
