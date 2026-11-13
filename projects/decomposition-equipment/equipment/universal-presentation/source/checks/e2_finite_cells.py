#!/usr/bin/env python3
"""Bounded, actual-cell E2 regressions. No theorem or freeness oracle.

All verification uses explicit exceptions, never optimization-sensitive assert.
The symbolic category test is deliberately a PREequipment test; it is not a
countermodel that pretends an arbitrary quotient of a full equipment is valid.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import product, combinations
from collections import Counter
import argparse
import json


class CheckFailure(RuntimeError):
    pass


COUNTS = Counter()
MUTATION = None


def require(ok, message):
    if not ok:
        raise CheckFailure(message)


def mul(a, b):
    return 2 if 2 in (a, b) else (a + b) % 2


def mprod(xs):
    answer = 0
    for x in xs:
        answer = mul(answer, x)
    return answer


@dataclass(frozen=True)
class Fn:
    dom: tuple
    cod: tuple
    values: tuple

    def __post_init__(self):
        require(len(self.dom) == len(self.values), "function domain length")
        require(all(v in self.cod for v in self.values), "function codomain")

    def __call__(self, x):
        return self.values[self.dom.index(x)]


def fn(dom, cod, rule):
    return Fn(tuple(dom), tuple(cod), tuple(rule(x) for x in dom))


def ident(a):
    return Fn(a, a, a)


def comp(g, f):
    require(f.cod == g.dom, "composition middle type")
    return fn(f.dom, g.cod, lambda x: g(f(x)))


def maps(a, b):
    return (Fn(a, b, v) for v in product(b, repeat=len(a)))


@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple = ()

    def induced(self, subset):
        subset = tuple(sorted(subset))
        return Graph(len(subset), tuple((subset.index(i), subset.index(j))
                     for i, j in self.edges if i in subset and j in subset))


EMPTY = Graph(0)
POINT = Graph(1)


def graphs(bound):
    for n in range(bound + 1):
        possible = tuple(combinations(range(n), 2))
        for flags in product((0, 1), repeat=len(possible)):
            yield Graph(n, tuple(e for e, flag in zip(possible, flags) if flag))


def partitions(n, arity):
    for allocation in product(range(arity), repeat=n):
        yield tuple(tuple(i for i, a in enumerate(allocation) if a == j)
                    for j in range(arity))


@dataclass(frozen=True)
class Span:
    left: Fn
    right: Fn

    def __post_init__(self):
        require(self.left.dom == self.right.dom, "span common apex")

    @property
    def A(self):
        return self.left.cod

    @property
    def B(self):
        return self.right.cod

    @property
    def E(self):
        return self.left.dom


@dataclass(frozen=True)
class H:
    graph: Graph
    span: Span


def graph_span(f):
    return Span(ident(f.dom), f)


@lru_cache(None)
def tuples(path, source_object):
    if not path:
        return tuple((a,) for a in source_object)
    require(path[0].span.A == source_object, "path start")
    current = tuple((a,) for a in source_object)
    for h in path:
        current = tuple(z + (e, h.span.right(e)) for z in current
                        for e in h.span.E if h.span.left(e) == z[-1])
    for h, k in zip(path, path[1:]):
        require(h.span.B == k.span.A, "path shared interface")
    return current


@dataclass(frozen=True)
class Cell:
    path: tuple
    source_object: tuple
    target: H
    left: Fn
    right: Fn
    blocks: tuple
    coefficient: Fn
    scalar: int

    def __post_init__(self):
        end = self.path[-1].span.B if self.path else self.source_object
        require(self.left.dom == self.source_object and self.right.dom == end,
                "cell domain boundaries")
        require(self.left.cod == self.target.span.A and self.right.cod == self.target.span.B,
                "cell target boundaries")
        require(self.coefficient.dom == tuples(self.path, self.source_object), "tuple map domain")
        require(self.coefficient.cod == self.target.span.E, "tuple map codomain")
        require(len(self.blocks) == len(self.path), "occurrence block count")
        flat = tuple(v for block in self.blocks for v in block)
        require(sorted(flat) == list(range(self.target.graph.n)), "actual partition cover")
        require(all(tuple(sorted(b)) == b for b in self.blocks), "ordered subset encoding")
        require(all(self.target.graph.induced(b) == h.graph
                    for b, h in zip(self.blocks, self.path)), "induced graph types")
        for z in self.coefficient.dom:
            e = self.coefficient(z)
            require(self.target.span.left(e) == self.left(z[0]), "cell left endpoint")
            require(self.target.span.right(e) == self.right(z[-1]), "cell right endpoint")
        require(self.scalar in (0, 1, 2), "C2 plus zero scalar")


def identity(h):
    p = (h,)
    return Cell(p, h.span.A, h, ident(h.span.A), ident(h.span.B),
                (tuple(range(h.graph.n)),),
                fn(tuples(p, h.span.A), h.span.E, lambda z: z[1]), 0)


def cell(path, source_object, target, left, right, blocks, rule, scalar=0):
    return Cell(tuple(path), source_object, target, left, right, tuple(blocks),
                fn(tuples(tuple(path), source_object), target.span.E, rule), scalar)


def substitute(outer, inners, empty_map=None):
    require(len(inners) == len(outer.path), "substitution arity")
    if not inners:
        require(empty_map is not None and empty_map.cod == outer.source_object,
                "nullary shared vertical map retained")
        return cell((), empty_map.dom, outer.target,
                    comp(outer.left, empty_map), comp(outer.right, empty_map), (),
                    lambda z: outer.coefficient((empty_map(z[0]),)), outer.scalar)
    require(all(c.target == h for c, h in zip(inners, outer.path)), "substitution targets")
    require(all(a.right == b.left for a, b in zip(inners, inners[1:])),
            "substitution SAME shared boundary map")
    path = tuple(h for c in inners for h in c.path)
    blocks = tuple(tuple(outer.blocks[i][v] for v in b)
                   for i, c in enumerate(inners) for b in c.blocks)
    def evaluate(z):
        pos = 0
        image = (inners[0].left(z[0]),)
        for c in inners:
            run = z[2 * pos:2 * (pos + len(c.path)) + 1]
            image += (c.coefficient(run), c.right(run[-1]))
            pos += len(c.path)
        return outer.coefficient(image)
    scalar = mprod([outer.scalar] + [c.scalar for c in inners])
    if MUTATION == "drop_nullary_scalar":
        scalar = mprod([outer.scalar] + [c.scalar for c in inners if c.path])
    return cell(path, inners[0].source_object, outer.target,
                comp(outer.left, inners[0].left), comp(outer.right, inners[-1].right),
                blocks, evaluate, scalar)


def all_cells(path, source_object, target, left, right):
    domain = tuples(tuple(path), source_object)
    fibres = tuple(tuple(e for e in target.span.E
                         if target.span.left(e) == left(z[0])
                         and target.span.right(e) == right(z[-1])) for z in domain)
    for blocks in partitions(target.graph.n, len(path)):
        if not all(target.graph.induced(b) == h.graph for b, h in zip(blocks, path)):
            continue
        for values in product(*fibres):
            for scalar in (0, 1, 2):
                yield Cell(tuple(path), source_object, target, left, right, blocks,
                           Fn(domain, target.span.E, values), scalar)


def restriction(h, f, g, choice):
    require(f.cod == h.span.A and g.cod == h.span.B, "restriction boundary type")
    apex = tuple(("R", choice, x, e, y) for x in f.dom for e in h.span.E for y in g.dom
                 if f(x) == h.span.left(e) and g(y) == h.span.right(e))
    r = H(h.graph, Span(fn(apex, f.dom, lambda v: v[2]), fn(apex, g.dom, lambda v: v[4])))
    kappa = cell((r,), f.dom, h, f, g, (tuple(range(h.graph.n)),),
                 lambda z: z[1][3], choice % 2)
    return r, kappa


def lift(alpha, f, g, h, k, choice):
    r, kappa = restriction(alpha.target, f, g, choice)
    require(comp(f, h) == alpha.left and comp(g, k) == alpha.right, "lift boundary factoring")
    scalar = mul(alpha.scalar, kappa.scalar)
    if MUTATION == "drop_choice_scalar":
        scalar = alpha.scalar
    return cell(alpha.path, alpha.source_object, r, h, k, alpha.blocks,
                lambda z: ("R", choice, h(z[0]), alpha.coefficient(z), k(z[-1])), scalar)


def unit(a, choice):
    apex = tuple(("I", choice, x) for x in a)
    u = H(EMPTY, Span(fn(apex, a, lambda v: v[2]), fn(apex, a, lambda v: v[2])))
    eta = cell((), a, u, ident(a), ident(a), (), lambda z: ("I", choice, z[0]), choice % 2)
    return u, eta


def unit_factor(alpha, position, choice):
    a = alpha.source_object if position == 0 else alpha.path[position - 1].span.B
    u, eta = unit(a, choice)
    path = alpha.path[:position] + (u,) + alpha.path[position:]
    blocks = alpha.blocks[:position] + ((),) + alpha.blocks[position:]
    def erase(z):
        p = 2 * position
        return z[:p + 1] + z[p + 3:]
    return cell(path, alpha.source_object, alpha.target, alpha.left, alpha.right,
                blocks, lambda z: alpha.coefficient(erase(z)), mul(alpha.scalar, eta.scalar))


def refinement_record(row):
    if MUTATION == "forget_refinement_slots":
        return tuple(sorted(c.scalar for c in row))
    return tuple(row)


def semantic_sentinels():
    """Fast adversarial examples exercise the SAME semantic implementation."""
    h = original_horizontal(POINT, 0, 0)
    f = ident(h.span.A)
    alpha = identity(h)
    r, k = restriction(h, f, f, 1)
    candidate = lift(alpha, f, f, f, f, 1)
    require(substitute(k, [candidate]) == alpha, "sentinel: chosen scalar must invert")
    binary = original_direct(EMPTY, ((), ()), (0, 0, 0), 0)
    nullary = original_direct(EMPTY, (), (0,), 1)
    require(substitute(binary, [nullary, identity(binary.path[1])]).scalar == 1,
            "sentinel: nullary child scalar must survive")
    x = identity(h)
    y = Cell(x.path, x.source_object, x.target, x.left, x.right,
             x.blocks, x.coefficient, 1)
    require(refinement_record((x, y)) != refinement_record((y, x)),
            "sentinel: repeated-slot ordered refinement record must survive")
    graph = Graph(2)
    p = original_direct(graph, ((0,), (1,)), (0, 0, 0), 0)
    q = original_direct(graph, ((1,), (0,)), (0, 0, 0), 0)
    require(p != q, "sentinel: actual ordered partition must survive")


def test_iterated_restrictions():
    A = (0, 1)
    E = ("x", "y")
    target = H(POINT, Span(fn(E, A, lambda e: E.index(e)),
                           fn(E, A, lambda _: 0)))
    for f, g, h in product(tuple(maps(A, A)), repeat=3):
        r1, k1 = restriction(target, f, f, 0)
        r2, k2 = restriction(r1, g, g, 1)
        r3, k3 = restriction(r2, h, h, 2)
        fg, gh, fgh = comp(f, g), comp(g, h), comp(f, comp(g, h))
        direct, kd = restriction(target, fgh, fgh, 1)
        chain = substitute(k1, [substitute(k2, [k3])])
        c = lift(chain, fgh, fgh, ident(A), ident(A), 1)
        # First collapse the last two restriction stages, then the first.
        r23, k23 = restriction(r1, gh, gh, 2)
        c23 = lift(substitute(k2, [k3]), gh, gh, ident(A), ident(A), 2)
        c1_23 = lift(substitute(k1, [k23]), fgh, fgh, ident(A), ident(A), 1)
        require(substitute(c1_23, [c23]) == c,
                "iterated restriction first associativity route")
        # First collapse stages 1 and 2, restrict its actual comparison by h.
        r12, k12 = restriction(target, fg, fg, 1)
        c12 = lift(substitute(k1, [k2]), fg, fg, ident(A), ident(A), 1)
        r12_3, k12_3 = restriction(r12, h, h, 0)
        rc12 = lift(substitute(c12, [k3]), h, h, ident(A), ident(A), 0)
        c12_3 = lift(substitute(k12, [k12_3]), fgh, fgh, ident(A), ident(A), 1)
        require(substitute(c12_3, [rc12]) == c,
                "iterated restriction second associativity route")
        COUNTS["iterated_restriction_three_stage_coherences"] += 2


def test_transformation_factor_squares():
    """Finite diagram components, not a claim to enumerate functors on FinSet."""
    A = (0, 1)
    h = H(POINT, graph_span(ident(A)))
    fs = tuple(maps(A, A))
    for Ff, Gf, tau_A, tau_X in product(fs, repeat=4):
        if comp(tau_A, Ff) != comp(Gf, tau_X):
            continue
        tau_H = cell((h,), A, h, tau_A, tau_A, ((0,),), lambda z: tau_A(z[1]))
        rF, kF = restriction(h, Ff, Ff, 0)
        rG, kG = restriction(h, Gf, Gf, 1)
        naturality_rhs = substitute(tau_H, [kF])
        tau_R = lift(naturality_rhs, Gf, Gf, tau_X, tau_X, 1)
        require(substitute(kG, [tau_R]) == naturality_rhs,
                "transformation restriction component actual naturality factor")
        expected = tuple(("R", 1, tau_X(z[1][2]), tau_A(z[1][3]), tau_X(z[1][4]))
                         for z in tau_R.coefficient.dom)
        require(tau_R.coefficient.values == expected, "transformation explicit apex formula")
        etaF, etaG = unit(A, 0)[1], unit(A, 1)[1]
        whiskered = substitute(etaG, [], empty_map=tau_A)
        tau_I = unit_factor(whiskered, 0, 0)
        require(substitute(tau_I, [etaF]) == whiskered,
                "transformation unit component actual naturality factor")
        COUNTS["transformation_finite_diagram_naturality_squares"] += 2
        if len(set(tau_A.values)) < len(A) or len(set(tau_X.values)) < len(A):
            COUNTS["noninvertible_transformation_diagram_instances"] += 1
    rs = [restriction(h, ident(A), ident(A), i) for i in range(3)]
    def component(tau, i, j):
        tau_H = cell((h,), A, h, tau, tau, ((0,),), lambda z: tau(z[1]))
        return lift(substitute(tau_H, [rs[i][1]]), ident(A), ident(A), tau, tau, j)
    for tau, sigma in product(fs, repeat=2):
        first = component(tau, 0, 1)
        second = component(sigma, 1, 2)
        require(substitute(second, [first]) == component(comp(sigma, tau), 0, 2),
                "extension preserves actual composition of transformation components")
        COUNTS["transformation_component_composition_equalities"] += 1


def test_universal_cell_classification():
    one = ("*",)
    source_targets = []
    for n in range(4):
        E = tuple(range(n))
        source_targets.append(H(POINT, Span(fn(E, one, lambda _: "*"),
                                            fn(E, one, lambda _: "*"))))
    cases = [(s, t, ident(one), ident(one)) for s, t in product(source_targets, repeat=2)]
    A = (0, 1)
    terminal = fn(A, one, lambda _: "*")
    target = source_targets[1]
    restricted, _ = restriction(target, terminal, terminal, 0)
    for apex in (restricted.span.E, restricted.span.E[:-1],
                 restricted.span.E + (("extra", 0, 0),)):
        def endpoint(e, side):
            return e[2 if side == 0 else 4] if e[0] == "R" else 0
        source = H(POINT, Span(fn(apex, A, lambda e: endpoint(e, 0)),
                               fn(apex, A, lambda e: endpoint(e, 1))))
        cases.append((source, target, terminal, terminal))
    for source, target, f, g in cases:
        pullback, _ = restriction(target, f, g, 0)
        for kappa in all_cells((source,), source.span.A, target, f, g):
            induced = tuple(("R", 0, source.span.left(e),
                             kappa.coefficient((source.span.left(e), e, source.span.right(e))),
                             source.span.right(e)) for e in source.span.E)
            predicted = (len(induced) == len(set(induced)) and
                         set(induced) == set(pullback.span.E) and kappa.scalar != 2)
            probe_bijective = True
            for x, y, E in product(source.span.A, source.span.B, ((), ("probe",))):
                probe = H(POINT, Span(fn(E, source.span.A, lambda _: x),
                                      fn(E, source.span.B, lambda _: y)))
                domain = list(all_cells((probe,), source.span.A, source,
                                        ident(source.span.A), ident(source.span.B)))
                codomain = set(all_cells((probe,), source.span.A, target, f, g))
                image = [substitute(kappa, [beta]) for beta in domain]
                probe_bijective &= len(image) == len(set(image)) and set(image) == codomain
                COUNTS["cartesian_actual_probe_fibres"] += 1
            require(predicted == probe_bijective,
                    "actual cartesian probe classification: pullback bijection AND scalar unit")
            COUNTS["cartesian_candidate_cells"] += 1
    # Detect extra off-diagonal witnesses as well as missing/duplicated diagonal ones.
    for size in range(3):
        A = tuple(range(size))
        target_apex = ("x", "y")
        target = H(EMPTY, Span(fn(target_apex, one, lambda _: "*"),
                               fn(target_apex, one, lambda _: "*")))
        out = fn(A, one, lambda _: "*")
        for n in range(4):
            E = tuple(range(n))
            for left, right in product(tuple(maps(E, A)), repeat=2):
                u = H(EMPTY, Span(left, right))
                for eta in all_cells((), A, u, ident(A), ident(A)):
                    predicted = (len(set(eta.coefficient.values)) == len(E) == len(A)
                                 and eta.scalar != 2)
                    domain = list(all_cells((u,), A, target, out, out))
                    codomain = set(all_cells((), A, target, out, out))
                    image = [substitute(alpha, [eta]) for alpha in domain]
                    actual = len(image) == len(set(image)) and set(image) == codomain
                    require(actual == predicted,
                            "actual unit probe classification: identity span AND scalar unit")
                    COUNTS["unit_candidate_cells"] += 1


def test_restrictions_and_units():
    a = (0, 1)
    one = ("*",)
    e = ("x", "y")
    target_spans = (
        Span(fn(e, one, lambda _: "*"), fn(e, one, lambda _: "*")),
        Span(fn(e, a, lambda x: e.index(x)), fn(e, a, lambda _: 0)),
        Span(fn((), a, lambda _: None), fn((), a, lambda _: None)),
    )
    for s in target_spans:
        for X in ((), (0,), a):
            for Y in ((), (0,), a):
                for f in maps(X, s.A):
                    for g in maps(Y, s.B):
                        for graph in (EMPTY, POINT):
                            target = H(graph, s)
                            restricted = [restriction(target, f, g, i) for i in range(3)]
                            COUNTS["restriction_choice_triples"] += 1
                            cs = {}
                            for i in range(3):
                                for j in range(3):
                                    ri, ki = restricted[i]
                                    cj = lift(ki, f, g, ident(X), ident(Y), j)
                                    require(substitute(restricted[j][1], [cj]) == ki,
                                            "restriction comparison factor equation")
                                    cs[i, j] = cj
                                    COUNTS["restriction_comparison_maps"] += 1
                            for i, j, k in product(range(3), repeat=3):
                                require(substitute(cs[j, k], [cs[i, j]]) == cs[i, k],
                                        "three-choice restriction cocycle")
                                COUNTS["restriction_cocycle_equalities"] += 1
                            # Every cell in these nullary/unary/binary profiles, not a selected map.
                            r0, k0 = restricted[0]
                            profiles = [((r0,), X)]
                            if X == Y:
                                empty = H(EMPTY, graph_span(ident(X)))
                                profiles += [((empty, r0), X), ((r0, empty), X)]
                                if graph == EMPTY:
                                    profiles += [((), X)]
                            for path, start in profiles:
                                for beta in all_cells(path, start, r0, ident(X), ident(Y)):
                                    alpha = substitute(k0, [beta])
                                    for choice in (0, 1, 2):
                                        lifted = lift(alpha, f, g, ident(X), ident(Y), choice)
                                        require(substitute(restricted[choice][1], [lifted]) == alpha,
                                                "restriction beta including nullary")
                                        require(lift(substitute(restricted[choice][1], [lifted]),
                                                     f, g, ident(X), ident(Y), choice) == lifted,
                                                "restriction eta including nullary")
                                        COUNTS["actual_restriction_factor_cells"] += 1
    # Unit bijections in nontrivial surrounding contexts, all coefficient maps.
    s = Span(fn(e, one, lambda _: "*"), fn(e, one, lambda _: "*"))
    q = H(EMPTY, s)
    for arity in range(4):
        path = (q,) * arity
        for alpha in all_cells(path, one, q, ident(one), ident(one)):
            for position in range(arity + 1):
                for choice in range(3):
                    factored = unit_factor(alpha, position, choice)
                    row = [identity(h) for h in alpha.path]
                    row.insert(position, unit(one, choice)[1])
                    require(substitute(factored, row) == alpha, "contextual unit beta")
                    for j in range(arity + 1):
                        # Insert units in the same final two named positions by either order.
                        left = unit_factor(unit_factor(alpha, position, choice),
                                           j + (j >= position), 0)
                        right = unit_factor(unit_factor(alpha, j, 0),
                                            position + (position > j), choice)
                        require(left == right, "two-unit context insertion coherence")
                        COUNTS["contextual_unit_coherence_equalities"] += 1
                    COUNTS["contextual_unit_factor_cells"] += 1
    for A in ((), (0,), a):
        us = [unit(A, i) for i in range(3)]
        comparison = {(i, j): unit_factor(us[j][1], 0, i)
                      for i in range(3) for j in range(3)}
        for i, j, k in product(range(3), repeat=3):
            require(substitute(comparison[j, k], [comparison[i, j]]) == comparison[i, k],
                    "unit change cocycle")
            COUNTS["unit_choice_cocycle_equalities"] += 1
        for B in ((), (0,), a):
            for f in maps(A, B):
                for i, j in product(range(3), repeat=2):
                    ui, _ = unit(B, i)
                    uj, _ = unit(B, j)
                    ri, ki = restriction(ui, f, f, i)
                    rj, kj = restriction(uj, f, f, j)
                    c = unit_factor(unit(B, j)[1], 0, i)
                    alpha = substitute(c, [ki])
                    rc = lift(alpha, f, f, ident(A), ident(A), j)
                    require(substitute(kj, [rc]) == alpha, "unit/restriction mixed factor")
                    COUNTS["mixed_unit_restriction_comparisons"] += 1
    # Not an illicit equality of original loop, new unit and noninjective pullback.
    f = fn(a, one, lambda _: "*")
    pulled, _ = restriction(unit(one, 0)[0], f, f, 0)
    require(len(pulled.span.E) == 4 and len(unit(a, 0)[0].span.E) == 2,
            "noninjective unit diagonal is not surjective")


def original_horizontal(graph, i, j):
    # Regular realization of K=[2]: F(i) has exactly i+1 tagged arrows into i.
    A = tuple((i, k) for k in range(i + 1))
    B = tuple((j, k) for k in range(j + 1))
    f = fn(A, B, lambda x: (j, x[1]))
    return H(graph, graph_span(f))


def original_direct(graph, blocks, chain, scalar):
    if MUTATION == "forget_partition_order":
        blocks = tuple(sorted(blocks))
    path = tuple(original_horizontal(graph.induced(block), chain[i], chain[i + 1])
                 for i, block in enumerate(blocks))
    target = original_horizontal(graph, chain[0], chain[-1])
    return cell(path, target.span.A, target, ident(target.span.A), ident(target.span.B),
                blocks, lambda z: z[0], scalar)


def original_compile(graph, blocks, chain, scalar):
    """Evaluate a right-comb term built ONLY from original C,U,D and identities."""
    n = len(blocks)
    if n == 0:
        require(graph == EMPTY, "C5 nullary whole")
        answer = original_direct(graph, (), chain, 0)  # original U_A generator
    elif n == 1:
        answer = identity(original_horizontal(graph, chain[0], chain[1]))
    else:
        first, rest = blocks[0], tuple(sorted(v for b in blocks[1:] for v in b))
        root = original_direct(graph, (first, rest), (chain[0], chain[1], chain[-1]), 0)
        child_blocks = tuple(tuple(rest.index(v) for v in b) for b in blocks[1:])
        rhs = original_compile(graph.induced(rest), child_blocks, chain[1:], 0)
        answer = substitute(root, [identity(root.path[0]), rhs])
    decoration = identity(answer.target)
    decoration = Cell(decoration.path, decoration.source_object, decoration.target,
                      decoration.left, decoration.right, decoration.blocks,
                      decoration.coefficient, scalar)
    return substitute(decoration, [answer])


def test_original_cells_and_refinements():
    for graph in graphs(3):
        for arity in range(4):
            for blocks in partitions(graph.n, arity):
                for chain in product(range(3), repeat=arity + 1):
                    if tuple(sorted(chain)) != chain:
                        continue
                    for scalar in (0, 1, 2):
                        direct = original_direct(graph, blocks, chain, scalar)
                        evaluated = original_compile(graph, blocks, chain, scalar)
                        require(evaluated == direct, "C/U/D compiler versus actual partition and map")
                        COUNTS["original_C5_compiled_cells"] += 1
    # Actual refinement arrows are ordered tuples, not just aggregate composites.
    graph = Graph(2)
    outer = original_direct(graph, ((0,), (1,)), (0, 0, 0), 0)
    tuples_seen = set()
    composites = Counter()
    for s, t in product((0, 1, 2), repeat=2):
        row = tuple(Cell(c.path, c.source_object, c.target, c.left, c.right,
                         c.blocks, c.coefficient, v)
                    for c, v in zip(map(identity, outer.path), (s, t)))
        key = refinement_record(row)
        tuples_seen.add(key)
        composites[substitute(outer, row)] += 1
    require(len(tuples_seen) == 9, "ordered repeated-slot refinement tuples retained")
    require(sorted(composites.values()) == [2, 2, 5], "noncancellative scalar fibre counts")
    COUNTS["ordered_scalar_refinement_tuples"] += len(tuples_seen)
    # Genuine nullary insertion carries scalar; repeated empty leaves are not removed.
    binary = original_direct(EMPTY, ((), ()), (0, 0, 0), 0)
    nullary = original_direct(EMPTY, (), (0,), 1)
    result = substitute(binary, [nullary, identity(binary.path[1])])
    require(len(result.path) == 1 and result.scalar == 1, "nontrivial nullary scalar survives")
    require(result == original_direct(EMPTY, ((),), (0, 0), 1), "UL with decoration retained")
    require(binary.path[0] == binary.path[1] and len(binary.blocks) == 2,
            "repeated empty occurrence positions retained")
    # Distinct graph cuts with equal repeated input types remain distinct.
    g = Graph(4, ((0, 2), (0, 3), (1, 2), (1, 3)))
    p = original_direct(g, ((0, 1), (2, 3)), (0, 0, 0), 0)
    q = original_direct(g, ((2, 3), (0, 1)), (0, 0, 0), 0)
    require(p.path == q.path and p != q, "actual K2,2 ordered partition distinction")
    COUNTS["repeated_nonempty_partition_witnesses"] += 2


def test_original_local_relations():
    for graph in graphs(3):
        for blocks in partitions(graph.n, 3):
            U, V, W = blocks
            X = tuple(sorted(U + V))
            for chain in product(range(3), repeat=4):
                if tuple(sorted(chain)) != chain:
                    continue
                root = original_direct(graph, (X, W), (chain[0], chain[2], chain[3]), 0)
                inner = original_direct(graph.induced(X),
                                        (tuple(X.index(v) for v in U), tuple(X.index(v) for v in V)),
                                        chain[:3], 0)
                left = substitute(root, [inner, identity(root.path[1])])
                right = original_compile(graph, blocks, chain, 0)
                require(left == right, "original local R with actual induced subsets")
                COUNTS["original_R_instances"] += 1
        for i in range(3):
            for j in range(i, 3):
                h = original_horizontal(graph, i, j)
                left_cut = original_direct(graph, ((), tuple(range(graph.n))), (i, i, j), 0)
                right_cut = original_direct(graph, (tuple(range(graph.n)), ()), (i, j, j), 0)
                require(substitute(left_cut, [original_direct(EMPTY, (), (i,), 0), identity(h)]) == identity(h),
                        "original local UL")
                require(substitute(right_cut, [identity(h), original_direct(EMPTY, (), (j,), 0)]) == identity(h),
                        "original local UR")
                COUNTS["original_UL_UR_instances"] += 2
                for a, b in product((0, 1, 2), repeat=2):
                    da = original_direct(graph, (tuple(range(graph.n)),), (i, j), a)
                    db = original_direct(graph, (tuple(range(graph.n)),), (i, j), b)
                    require(substitute(da, [db]) == original_direct(graph, (tuple(range(graph.n)),), (i, j), mul(a, b)),
                            "original local DA and D0")
                    COUNTS["original_DA_D0_instances"] += 1
                for m in (0, 1, 2):
                    d = original_direct(graph, (tuple(range(graph.n)),), (i, j), m)
                    left_d = original_direct(EMPTY, ((),), (i, i), m)
                    right_d = original_direct(EMPTY, ((),), (j, j), m)
                    require(substitute(left_cut, [left_d, identity(h)]) == substitute(d, [left_cut]),
                            "original local DL at repeated/empty slot")
                    require(substitute(right_cut, [identity(h), right_d]) == substitute(d, [right_cut]),
                            "original local DR at repeated/empty slot")
                    COUNTS["original_DL_DR_instances"] += 2


def tuple_horizontal(graph, path, start):
    apex = tuples(tuple(path), start)
    end = path[-1].span.B if path else start
    return H(graph, Span(fn(apex, start, lambda z: z[0]), fn(apex, end, lambda z: z[-1])))


def extended_flat_compile(graph, blocks, path, start):
    """Local EXT binary c/c0 and unary span-square u, actual nested tuple apices."""
    flat = tuple_horizontal(graph, path, start)
    if not path:
        primitive = H(EMPTY, graph_span(ident(start)))
        c0 = cell((), start, primitive, ident(start), ident(start), (), lambda z: z[0])
        encoding = cell((primitive,), start, flat, ident(start), ident(start), ((),),
                        lambda z: (z[1],))
        return substitute(encoding, [c0])
    if len(path) == 1:
        # The actual j_S square, not pretending the tuple apex equals the old apex.
        return cell(path, start, flat, ident(start), ident(path[-1].span.B), blocks, lambda z: z)
    first = blocks[0]
    rest = tuple(sorted(v for b in blocks[1:] for v in b))
    child_blocks = tuple(tuple(rest.index(v) for v in b) for b in blocks[1:])
    child = extended_flat_compile(graph.induced(rest), child_blocks, path[1:], path[0].span.B)
    inputs = (path[0], child.target)
    nested = tuple_horizontal(graph, inputs, start)
    cut = cell(inputs, start, nested, ident(start), ident(path[-1].span.B),
               (first, rest), lambda z: z)
    tree = substitute(cut, [identity(path[0]), child])
    flatten = cell((nested,), start, flat, ident(start), ident(path[-1].span.B),
                   (tuple(range(graph.n)),), lambda z: z[1][:2] + z[1][3])
    return substitute(flatten, [tree])


def extended_compile(alpha):
    flat = extended_flat_compile(alpha.target.graph, alpha.blocks, alpha.path, alpha.source_object)
    square = cell((flat.target,), alpha.source_object, alpha.target, alpha.left, alpha.right,
                  (tuple(range(alpha.target.graph.n)),),
                  lambda z: alpha.coefficient(z[1]), alpha.scalar)
    return substitute(square, [flat])


def test_extended_local_compiler():
    one = ("*",)
    E = ("x", "y")
    span = Span(fn(E, one, lambda _: "*"), fn(E, one, lambda _: "*"))
    for graph in graphs(2):
        target = H(graph, span)
        for arity in range(4):
            for blocks in partitions(graph.n, arity):
                path = tuple(H(graph.induced(b), span) for b in blocks)
                domain = tuples(path, one)
                for values in product(E, repeat=len(domain)):
                    for scalar in (0, 1, 2):
                        alpha = Cell(path, one, target, ident(one), ident(one), blocks,
                                     Fn(domain, E, values), scalar)
                        require(extended_compile(alpha) == alpha,
                                "EXT local-generator compiler versus full actual witness map")
                        COUNTS["extended_locally_compiled_cells"] += 1
    # The nullary square preserves different outer boundaries and its actual map.
    A = (0, 1)
    target = H(EMPTY, Span(fn(E, A, lambda x: E.index(x)), fn(E, A, lambda x: 1 - E.index(x))))
    alpha = cell((), A, target, ident(A), fn(A, A, lambda x: 1 - x), (), lambda z: E[z[0]], 2)
    require(extended_compile(alpha) == alpha, "EXT nonidentity nullary coefficient square")
    COUNTS["extended_locally_compiled_cells"] += 1


def test_nullary_boundary_and_noninjective_naturality():
    A, B = (0, 1), ("a", "b")
    E = ("e", "f")
    s = Span(fn(E, B, lambda x: "a" if x == "e" else "b"),
             fn(E, B, lambda x: "b" if x == "e" else "a"))
    h = H(EMPTY, s)
    left = fn(A, B, lambda x: B[x])
    right = fn(A, B, lambda x: B[1 - x])
    alpha = cell((), A, h, left, right, (), lambda z: E[z[0]], 1)
    for C in ((), (0,), (0, 1)):
        for f in maps(C, A):
            whiskered = substitute(alpha, [], empty_map=f)
            require(whiskered.left == comp(left, f) and whiskered.right == comp(right, f),
                    "nullary differing boundaries retain common precomposition map")
            require(whiskered.coefficient.values == tuple(E[f(x)] for x in C),
                    "nullary actual witness map precomposes")
            require(whiskered.scalar == 1, "nullary whisker retains scalar")
            COUNTS["nullary_common_boundary_whiskerings"] += 1
    # Distinct shared maps cannot be erased just because all apex maps are empty.
    C = ("*",)
    empty_A = H(EMPTY, Span(fn((), A, lambda _: None), fn((), A, lambda _: None)))
    empty_C = H(EMPTY, Span(fn((), C, lambda _: None), fn((), C, lambda _: None)))
    zero = fn(C, A, lambda _: 0)
    one = fn(C, A, lambda _: 1)
    outer = cell((empty_A, empty_A), A, empty_A, ident(A), ident(A), ((), ()), lambda z: None)
    first = cell((empty_C,), C, empty_A, zero, zero, ((),), lambda z: None)
    second = cell((empty_C,), C, empty_A, one, zero, ((),), lambda z: None)
    try:
        substitute(outer, [first, second])
    except CheckFailure as error:
        require(str(error) == "substitution SAME shared boundary map", "expected shared-map rejection")
    else:
        raise CheckFailure("empty-apex unmatched boundary row was accepted")
    COUNTS["empty_apex_unmatched_shared_map_rejections"] += 1


def test_preequipment_quotient_and_terminal_return():
    # Finite category paths, generated from actual graph edges, length at most 2
    # because the quiver is acyclic. This covers its ENTIRE ordinary substitution.
    objects = ("P", "R", "H")
    edges = {"a": ("P", "R"), "b": ("P", "R"), "k": ("R", "H")}
    paths = [(x, x, ()) for x in objects]
    paths += [(s, t, (name,)) for name, (s, t) in edges.items()]
    paths += [("P", "H", ("a", "k")), ("P", "H", ("b", "k"))]
    def equivalent(p, q, saturated=False):
        if p[:2] != q[:2]:
            return False
        if p == q:
            return True
        return (p[:2] == ("P", "H") or
                (saturated and p[:2] == ("P", "R")))
    def compose_path(q, p):
        require(p[1] == q[0], "path middle object")
        return (p[0], q[1], p[2] + q[2])
    for saturated in (False, True):
        for p, q in product(paths, repeat=2):
            if not equivalent(p, q, saturated):
                continue
            for r in paths:
                if p[1] == r[0]:
                    require(equivalent(compose_path(r, p), compose_path(r, q), saturated),
                            "preequipment ordinary right congruence")
                    COUNTS["preequipment_congruence_contexts"] += 1
                if r[1] == p[0]:
                    require(equivalent(compose_path(p, r), compose_path(q, r), saturated),
                            "preequipment ordinary left congruence")
                    COUNTS["preequipment_congruence_contexts"] += 1
    pa, pb = ("P", "R", ("a",)), ("P", "R", ("b",))
    ka, kb = ("P", "H", ("a", "k")), ("P", "H", ("b", "k"))
    require(equivalent(ka, kb) and not equivalent(pa, pb),
            "identified composites need not identify marked-candidate lifts")
    require(equivalent(pa, pb, True), "cartesian cancellation saturation merges lifts")
    COUNTS["preequipment_category_objects"] = len(objects)
    COUNTS["preequipment_category_arrows"] = len(paths)
    # NOGO's reference syntax has no nonidentity generator with output R_i.
    # Least reachability closure is a finite check of its constructor invariant,
    # not a bounded enumeration represented as a proof for arbitrary syntax.
    old_names = {"H1", "H2", "W", "old_empty"}
    generators = [("cut", ("H1", "H2"), "W"),
                  ("old_U", (), "old_empty"),
                  ("chi1", ("R1",), "H1"), ("chi2", ("R2",), "H2"),
                  ("chi", ("T",), "W"),
                  ("x", ("R1", "R2"), "T"), ("y", ("R1", "R2"), "T")]
    reachable = set(old_names)
    while True:
        new = reachable | {output for _, inputs, output in generators
                           if all(h in reachable for h in inputs)}
        if new == reachable:
            break
        reachable = new
    require(reachable == old_names, "NOGO preequipment all-old frontier cannot acquire R/T outputs")
    require(all(output not in ("R1", "R2") for _, _, output in generators),
            "NOGO no new restriction-output generator")
    COUNTS["NOGO_reference_generator_shapes"] = len(generators)
    # Actual graph-span terminal restrictions, section maps and return context.
    for r in (1, 2, 3):
        graph = Graph(2 * r, tuple((i, j) for i in range(r) for j in range(r, 2 * r)))
        old = [original_direct(graph, blocks, (0, 0, 0), 0)
               for blocks in ((tuple(range(r)), tuple(range(r, 2 * r))),
                              (tuple(range(r, 2 * r)), tuple(range(r))))]
        require(old[0] != old[1] and old[0].path == old[1].path, "distinct original whole cuts")
        one = old[0].source_object
        for size in (2, 3):
            sets = (one, tuple(range(size)), one)
            terminal = [fn(A, one, lambda _: one[0]) for A in sets]
            sections = [fn(one, A, lambda _, A=A: A[0]) for A in sets]
            ris = [restriction(h, terminal[i], terminal[i + 1], 0)
                   for i, h in enumerate(old[0].path)]
            rt, kt = restriction(old[0].target, terminal[0], terminal[2], 0)
            returns = [lift(identity(h), terminal[i], terminal[i + 1], sections[i], sections[i + 1], 0)
                       for i, h in enumerate(old[0].path)]
            restrictions = []
            for alpha in old:
                incoming = substitute(alpha, [k for _, k in ris])
                lifted = lift(incoming, terminal[0], terminal[2], ident(sets[0]), ident(sets[2]), 0)
                returned = substitute(kt, [substitute(lifted, returns)])
                require(returned == alpha, "terminal-restriction return context equals original cut")
                restrictions.append(lifted)
                COUNTS["terminal_return_actual_cell_equalities"] += 1
            require(restrictions[0] != restrictions[1], "restrictions retain old cut distinction")
            # Their span maps agree; no spurious claim that they are equal cells.
            require(restrictions[0].coefficient == restrictions[1].coefficient,
                    "paired partition quotient would merge cells with same coefficient")


def scalar_class(graph, scalar):
    return scalar if graph.n == 0 or scalar == 2 else 0


def quotient_key(alpha, doctrine):
    coefficient = alpha.coefficient
    scalar = alpha.scalar
    if doctrine == "QI" and alpha.target.graph.n:
        coefficient = None
    if doctrine == "QH":
        scalar = scalar_class(alpha.target.graph, scalar)
    return (alpha.path, alpha.source_object, alpha.target, alpha.left, alpha.right,
            alpha.blocks, coefficient, scalar)


def test_positive_quotient_factor_maps():
    one, A, E = ("*",), (0, 1), ("x", "y")
    span = Span(fn(E, one, lambda _: "*"), fn(E, one, lambda _: "*"))
    terminal = fn(A, one, lambda _: "*")
    section = fn(one, A, lambda _: 0)
    for graph in (EMPTY, POINT):
        target = H(graph, span)
        source = H(graph, span)
        cells = list(all_cells((source,), one, target, ident(one), ident(one)))
        for doctrine in ("QI", "QH"):
            for alpha, beta in product(cells, repeat=2):
                equal = quotient_key(alpha, doctrine) == quotient_key(beta, doctrine)
                for choice in range(3):
                    la = lift(alpha, terminal, terminal, section, section, choice)
                    lb = lift(beta, terminal, terminal, section, section, choice)
                    require((quotient_key(la, doctrine) == quotient_key(lb, doctrine)) == equal,
                            "positive quotient restriction factor reflects/preserves class")
                    ua = unit_factor(alpha, 0, choice)
                    ub = unit_factor(beta, 0, choice)
                    require((quotient_key(ua, doctrine) == quotient_key(ub, doctrine)) == equal,
                            "positive quotient unit factor reflects/preserves class")
                    COUNTS["positive_quotient_factor_class_comparisons"] += 2
        # Actual one-slot substitution composition on the entire finite unary fibre.
        for doctrine in ("QI", "QH"):
            for alpha, beta in product(cells, repeat=2):
                if quotient_key(alpha, doctrine) != quotient_key(beta, doctrine):
                    continue
                for outer in cells:
                    require(quotient_key(substitute(outer, [alpha]), doctrine) ==
                            quotient_key(substitute(outer, [beta]), doctrine),
                            "positive quotient actual unary substitution")
                    COUNTS["positive_quotient_unary_contexts"] += 1


def test_fresh_unit_word_separation():
    # Independently enumerable forest allocation in ENV's ordinary separating
    # model. Empty graph LETTER is not the empty graph WORD.
    def forest_allocations(source_length, target_length):
        return tuple(lengths for lengths in product(range(source_length + 1), repeat=target_length)
                     if sum(lengths) == source_length)
    require(len(forest_allocations(0, 1)) == 1, "old empty graph receives actual nullary forest")
    require(len(forest_allocations(1, 0)) == 0, "old empty graph letter cannot map back to fresh unit")
    for s, t in product(range(4), repeat=2):
        COUNTS["ordinary_empty_graph_forest_allocations"] += len(forest_allocations(s, t))


def test_positive_scalar_quotient():
    # Q_H with H=C2 on every nonempty graph, exact at the empty graph.
    checked = 0
    for graph in graphs(3):
        for arity in range(4):
            for blocks in partitions(graph.n, arity):
                outer = original_direct(graph, blocks, (0,) * (arity + 1), 0)
                for a in (0, 1, 2):
                    for row_scalars in product((0, 1, 2), repeat=arity):
                        composite_scalar = mprod((a,) + row_scalars)
                        for target in (0, 1, 2):
                            if scalar_class(graph, composite_scalar) != scalar_class(graph, target):
                                continue
                            adjusted = None
                            for candidates in product((0, 1, 2), repeat=arity):
                                if all(scalar_class(h.graph, x) == scalar_class(h.graph, y)
                                       for h, x, y in zip(outer.path, row_scalars, candidates)):
                                    if mprod((a,) + candidates) == target:
                                        adjusted = candidates
                                        break
                            require(adjusted is not None, "Q_H actual fixed-endpoint scalar forest lift")
                            if arity == 0:
                                require(composite_scalar == target, "Q_H nullary scalar exactness")
                            checked += 1
    COUNTS["positive_QH_fixed_endpoint_forest_instances"] = checked
    require(scalar_class(EMPTY, 0) != scalar_class(EMPTY, 1), "empty nullary scalar not collapsed")
    require(scalar_class(POINT, 0) == scalar_class(POINT, 1), "nonempty unit subgroup quotient nontrivial")
    require(scalar_class(POINT, 0) != scalar_class(POINT, 2), "absorbing zero not unit gauge")


def run():
    semantic_sentinels()
    test_restrictions_and_units()
    test_iterated_restrictions()
    test_transformation_factor_squares()
    test_universal_cell_classification()
    test_original_cells_and_refinements()
    test_original_local_relations()
    test_extended_local_compiler()
    test_nullary_boundary_and_noninjective_naturality()
    test_preequipment_quotient_and_terminal_return()
    test_positive_scalar_quotient()
    test_positive_quotient_factor_maps()
    test_fresh_unit_word_separation()
    return {"status": "PASS", "scope": "finite regression evidence, NOT a proof of universal presentation or all-cell generation",
            "domains": {"original_graphs": "all simple ordered graphs on 0..3 vertices; K=[2]; arities 0..3",
                        "monoid": "C2 plus absorbing zero; 0=identity, 1=involution, 2=absorbing zero",
                        "restrictions": "3 explicitly listed target spans, all endpoint maps from sets of size 0..2, graphs empty/point, 3 tagged/scalar choices",
                        "unit_contexts": "all maps from paths of 0..3 repeated two-witness spans over singleton; every insertion position",
                        "obstruction": "entire 3-object 8-arrow acyclic preequipment category; actual K(r,r) terminal return for r=1,2,3 and middle sizes 2,3",
                        "quotient": "Q_H original scalar-forest fixed endpoints; not all generic quotient contexts",
                        "extended_compiler": "all simple ordered graphs on 0..2 vertices; arities0..3; two-witness singleton-endpoint span; every coefficient map and scalar",
                        "classification": "all singleton-endpoint span maps with 0..3 witnesses plus 3 noninjective restriction candidates; all candidate units on sets0..2 and apices0..3"},
            "counts": dict(sorted(COUNTS.items()))}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--mutate", choices=("drop_nullary_scalar", "drop_choice_scalar", "forget_refinement_slots", "forget_partition_order"))
    args = parser.parse_args()
    MUTATION = args.mutate
    try:
        result = run()
    except CheckFailure as error:
        print(json.dumps({"status": "REJECT", "mutation": MUTATION, "reason": str(error)}, sort_keys=True))
        raise SystemExit(1)
    print(json.dumps(result, sort_keys=True, indent=2))
