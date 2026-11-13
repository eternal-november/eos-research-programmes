#!/usr/bin/env python3
"""Exact, dependency-free checks for split-tuple joint realization.

Run with Python 3.10+ normally and with -O. All verdicts use explicit exceptions,
not `assert`. Every numeric datum is an int or fractions.Fraction; no floats or
numerical LP solver are used. This verifies witnesses and algebraic obstruction
certificates, not a general LP-feasibility or nonnegative-rank algorithm.
"""
from dataclasses import dataclass, replace
from fractions import Fraction as F
from itertools import product

ZERO = F(0)
ONE = F(1)


class CheckFailure(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise CheckFailure(message)


def equal(actual, expected, message):
    require(actual == expected, f"{message}: {actual!r} != {expected!r}")


def rational(value):
    require(isinstance(value, (int, F)), f"inexact input: {value!r}")
    return F(value)


def matrix(rows):
    return tuple(tuple(rational(x) for x in row) for row in rows)


def zeros(n, m):
    return matrix([[0] * m for _ in range(n)])


def matmul(a, b):
    require(a and b and len(a[0]) == len(b), "matrix shape mismatch")
    return matrix([[sum((a[i][k] * b[k][j] for k in range(len(b))), ZERO)
                    for j in range(len(b[0]))] for i in range(len(a))])


def transpose(a):
    return matrix(zip(*a))


def identity(n):
    return matrix([[int(i == j) for j in range(n)] for i in range(n)])


def determinant(a):
    require(a and all(len(row) == len(a) for row in a), "determinant shape")
    a = [list(row) for row in a]
    result = ONE
    for k in range(len(a)):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return ZERO
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        d = a[k][k]
        result *= d
        for i in range(k + 1, len(a)):
            ratio = a[i][k] / d
            for j in range(k + 1, len(a)):
                a[i][j] -= ratio * a[k][j]
            a[i][k] = ZERO
    return result


@dataclass(frozen=True)
class Local:
    A: tuple
    B: tuple


@dataclass(frozen=True)
class Problem:
    locals: tuple
    E: tuple
    S: tuple
    w: tuple
    Q: tuple
    R: tuple

    @property
    def J(self):
        return range(len(self.R))

    def validate(self):
        n = len(self.locals)
        require(n > 0 and self.E and self.S, "nonempty finite interfaces")
        equal(len(set(self.E)), len(self.E), "duplicate hidden tuples")
        equal(len(set(self.S)), len(self.S), "duplicate coarse tuples")
        require(self.R and self.R[0], "nonempty output interface")
        require(len(self.w) == len(self.S) == len(self.Q), "global shapes")
        for row in self.Q:
            equal(len(row), len(self.R[0]), "Q output width")
            equal(sum(row, ZERO), ONE, "Q normalization")
        for row in self.R:
            equal(len(row), len(self.R[0]), "R output width")
            require(sum(row, ZERO) >= 0, "nonnegative announcement mass")
        for value in self.w:
            require(value >= 0, "nonnegative retained coarse mass")
        equal(sum(self.w, ZERO), ONE, "w normalization")
        equal(sum((sum(row, ZERO) for row in self.R), ZERO), ONE, "R total mass")
        equal(tuple(sum((self.R[j][o] for j in self.J), ZERO)
                    for o in range(len(self.R[0]))),
              matmul((self.w,), self.Q)[0], "global output marginal")
        for i, local in enumerate(self.locals):
            require(local.A and local.B and local.B[0], "nonempty local matrices")
            equal(len(local.A), len(self.R), "local announcement height")
            nh, ns = len(local.B), len(local.B[0])
            for row in local.A:
                equal(len(row), nh, "A hidden width")
            for row in local.B:
                equal(len(row), ns, "B coarse width")
                equal(sum(row, ZERO), ONE, "B normalization")
            for j in self.J:
                equal(sum(local.A[j], ZERO), sum(self.R[j], ZERO), "local p")
            for h in self.E:
                require(len(h) == n and 0 <= h[i] < nh, "E coordinate")
            for s in self.S:
                require(len(s) == n and 0 <= s[i] < ns, "S coordinate")
            local_t = matmul(local.A, local.B)
            for t in range(ns):
                equal(sum((local_t[j][t] for j in self.J), ZERO),
                      sum((self.w[k] for k, s in enumerate(self.S) if s[i] == t), ZERO),
                      "local/global retained-state marginal")
        values = list(self.w)
        values += [x for m in (self.Q, self.R) for row in m for x in row]
        values += [x for loc in self.locals for m in (loc.A, loc.B) for row in m for x in row]
        require(all(isinstance(x, (int, F)) and x >= 0 for x in values),
                "nonnegative exact input coefficients")


def variables(problem):
    return tuple((j, h, s) for j in problem.J for h in problem.E for s in problem.S)


def linear_system(problem):
    """Return exact sparse rows (name, {Z-key: coefficient}, right-hand side)."""
    rows = []
    for j in problem.J:
        for h in problem.E:
            for i, loc in enumerate(problem.locals):
                for t in range(len(loc.B[0])):
                    coeff = {(j, h, s): F(int(s[i] == t)) - loc.B[h[i]][t]
                             for s in problem.S}
                    rows.append((("profile", j, h, i, t), coeff, ZERO))
        for i, loc in enumerate(problem.locals):
            for u in range(len(loc.B)):
                coeff = {(j, h, s): ONE for h in problem.E if h[i] == u for s in problem.S}
                rows.append((("hidden", j, i, u), coeff, loc.A[j][u]))
    for k, s in enumerate(problem.S):
        rows.append((("coarse", s), {(j, h, s): ONE for j in problem.J for h in problem.E},
                     problem.w[k]))
    for j in problem.J:
        for o in range(len(problem.R[0])):
            coeff = {(j, h, s): problem.Q[k][o] for h in problem.E for k, s in enumerate(problem.S)}
            rows.append((("output", j, o), coeff, problem.R[j][o]))
    return rows


def check_certificate(problem, z):
    problem.validate()
    keys = set(variables(problem))
    require(set(z) <= keys, "Z has a forbidden coordinate")
    require(all(isinstance(v, (int, F)) and v >= 0 for v in z.values()), "Z nonnegativity/exactness")
    for name, coefficients, rhs in linear_system(problem):
        actual = sum((c * z.get(key, ZERO) for key, c in coefficients.items()), ZERO)
        equal(actual, rhs, f"linear constraint {name}")
    return {(j, h): sum((z.get((j, h, s), ZERO) for s in problem.S), ZERO)
            for j in problem.J for h in problem.E}


def check_boolean_certificate(problem, z_support):
    """Check the Booleanized equations directly with existential quantification."""
    require(set(z_support) <= set(variables(problem)), "Boolean forbidden coordinate")
    active = {(j, h) for j, h, s in z_support}
    for j in problem.J:
        for h in problem.E:
            for i, loc in enumerate(problem.locals):
                for t in range(len(loc.B[0])):
                    actual = any((j, h, s) in z_support for s in problem.S if s[i] == t)
                    expected = (j, h) in active and loc.B[h[i]][t] > 0
                    equal(actual, expected, "Boolean profile")
        for i, loc in enumerate(problem.locals):
            for u in range(len(loc.B)):
                equal(any(jj == j and h[i] == u for jj, h in active),
                      loc.A[j][u] > 0, "Boolean hidden marginal")
    for k, s in enumerate(problem.S):
        equal(any(ss == s for jj, h, ss in z_support), problem.w[k] > 0, "Boolean coarse coverage")
    for j in problem.J:
        for o in range(len(problem.R[0])):
            equal(any((j, h, s) in z_support and problem.Q[k][o] > 0
                      for h in problem.E for k, s in enumerate(problem.S)),
                  problem.R[j][o] > 0, "Boolean output")


@dataclass(frozen=True)
class Implementation:
    labels: tuple
    A: tuple
    B: tuple


def selector(labels, coordinate, hidden_count):
    return matrix([[int(h[coordinate] == u) for u in range(hidden_count)] for j, h in labels])


def coordinate_projection(coarse_states, coordinate, size):
    return matrix([[int(s[coordinate] == t) for t in range(size)] for s in coarse_states])


def check_implementation(problem, impl):
    require(impl.labels, "implementation must have a middle state")
    equal(len(impl.A), len(problem.R), "implementation A height")
    equal(len(impl.B), len(impl.labels), "implementation B height")
    for row in impl.A:
        equal(len(row), len(impl.labels), "implementation A width")
    for row in impl.B:
        equal(len(row), len(problem.S), "implementation B width")
        equal(sum(row, ZERO), ONE, "implementation B normalized")
    require(all(isinstance(x, (int, F)) and x >= 0 for m in (impl.A, impl.B) for row in m for x in row),
            "implementation exact/nonnegative")
    require(all(h in problem.E for j, h in impl.labels), "implementation tuple allowance")
    for i, loc in enumerate(problem.locals):
        c = selector(impl.labels, i, len(loc.B))
        f = coordinate_projection(problem.S, i, len(loc.B[0]))
        equal(matmul(impl.A, c), loc.A, "A C_i = A_i")
        equal(matmul(impl.B, f), matmul(c, loc.B), "B F_i = C_i B_i")
    t = matmul(impl.A, impl.B)
    equal(tuple(sum((t[j][k] for j in problem.J), ZERO) for k in range(len(problem.S))),
          problem.w, "implementation coarse law")
    equal(matmul(t, problem.Q), problem.R, "implementation target law")


def normal_form(problem, z):
    alpha = check_certificate(problem, z)
    labels = tuple((j, h) for j in problem.J for h in problem.E if alpha[j, h] > 0)
    a = matrix([[alpha[jj, h] if j == jj else ZERO for jj, h in labels] for j in problem.J])
    b = matrix([[z.get((j, h, s), ZERO) / alpha[j, h] for s in problem.S] for j, h in labels])
    result = Implementation(labels, a, b)
    check_implementation(problem, result)
    return result


def certificate_from_implementation(problem, impl):
    check_implementation(problem, impl)
    z = {(j, h, s): sum((impl.A[j][v] * impl.B[v][k]
                        for v, (_, hh) in enumerate(impl.labels) if hh == h), ZERO)
         for j in problem.J for h in problem.E for k, s in enumerate(problem.S)}
    check_certificate(problem, z)
    return z


def check_round_trip(problem, z):
    impl = normal_form(problem, z)
    back = certificate_from_implementation(problem, impl)
    for key in variables(problem):
        equal(back[key], z.get(key, ZERO), "Z -> normal form -> Z")
    return impl


def check_equality_obstruction(problem, multipliers):
    """Verify sum y_r L_r = 0 but sum y_r b_r != 0, an exact LP obstruction."""
    problem.validate()
    rows = {name: (coeff, rhs) for name, coeff, rhs in linear_system(problem)}
    require(set(multipliers) <= set(rows), "unknown obstruction row")
    lhs = {key: ZERO for key in variables(problem)}
    rhs = ZERO
    for name, y in multipliers.items():
        coefficients, b = rows[name]
        rhs += y * b
        for key, coefficient in coefficients.items():
            lhs[key] += y * coefficient
    require(all(x == 0 for x in lhs.values()), "obstruction left side is not identically zero")
    require(rhs != 0, "obstruction has zero right side")
    return rhs


def diagonal_obstruction(problem, j, u):
    """Certificate for one positive hidden demand with no equal-profile partner.

    This uses S contained in the diagonal. Every allowed hidden tuple above
    local coordinate 0=u has incompatible B profiles. Profile row differences
    force its alpha to zero. Sum those equations and subtract its hidden demand.
    """
    require(all(len(set(s)) == 1 for s in problem.S), "not a shared diagonal interface")
    require(problem.locals[0].A[j][u] > 0, "need positive hidden demand")
    y = {("hidden", j, 0, u): -ONE}
    for h in problem.E:
        if h[0] != u:
            continue
        unequal = next(((i, t) for i, loc in enumerate(problem.locals[1:], 1)
                        for t in range(len(problem.locals[0].B[0]))
                        if loc.B[h[i]][t] != problem.locals[0].B[h[0]][t]), None)
        require(unequal is not None, "an equal-profile partner exists")
        i, t = unequal
        difference = problem.locals[i].B[h[i]][t] - problem.locals[0].B[h[0]][t]
        y["profile", j, h, 0, t] = ONE / difference
        y["profile", j, h, i, t] = -ONE / difference
    equal(check_equality_obstruction(problem, y), -problem.locals[0].A[j][u],
          "diagonal obstruction right side")
    return y


def correlation_example(m, epsilon):
    states = tuple(product(range(m), repeat=2))
    local = Local(matrix([[F(1, m)] for _ in range(m)]), matrix([[F(1, m)] * m]))
    beta = matrix([[(ONE - epsilon) * F(int(y == (x + j) % m), m) + epsilon / (m * m)
                    for x, y in states] for j in range(m)])
    r = matrix([[x / m for x in row] for row in beta])
    problem = Problem((local, local), ((0, 0),), states, tuple([F(1, m * m)] * len(states)),
                      identity(len(states)), r)
    z = {(j, (0, 0), s): r[j][k] for j in problem.J for k, s in enumerate(states)}
    impl = check_round_trip(problem, z)
    equal(len(impl.labels), m, "correlation implementation size")
    selected = matrix([[r[j][states.index((0, k))] for k in range(m)] for j in range(m)])
    det = determinant(selected)
    equal(det, (ONE - epsilon) ** (m - 1) / (m ** (2 * m)), "correlation rank minor")
    require(det > 0, "ordinary rank m lower bound")
    if epsilon:
        require(all(v > 0 for row in r for v in row), "full support correlation example")
    # One unsplit hidden tuple forces B=w and A=p, hence R=p*w when Q=I.
    independent = matrix([[F(1, m) * x for x in problem.w] for _ in range(m)])
    require(problem.R != independent, "unsplit singleton unexpectedly sufficient")
    return problem, z, det


def test_correlation_family():
    summaries = []
    for m in (2, 3, 5):
        for epsilon in (ZERO, F(1, 2)):
            _, _, det = correlation_example(m, epsilon)
            summaries.append(f"m={m}, eps={epsilon}, det={det}")
    return "; ".join(summaries)


def test_boolean_mismatch():
    a = matrix([[F(1, 2), F(1, 2)]])
    b1 = matrix([[F(1, 3), F(2, 3)], [F(2, 3), F(1, 3)]])
    b2 = tuple(reversed(b1))
    problem = Problem((Local(a, b1), Local(a, b2)), ((0, 0), (1, 1)),
                      ((0, 0), (1, 1)), (F(1, 2), F(1, 2)), matrix([[1], [1]]), matrix([[1]]))
    problem.validate()
    support = set(variables(problem))
    check_boolean_certificate(problem, support)
    diagonal_obstruction(problem, 0, 0)
    diagonal_obstruction(problem, 0, 1)
    # Removing the tied-hidden restriction repairs the stochastic problem.
    repaired = replace(problem, E=((0, 1), (1, 0)))
    z = {(0, h, s): F(1, 2) * b1[h[0]][s[0]] for h in repaired.E for s in repaired.S}
    check_round_trip(repaired, z)
    return "Boolean feasible; stochastic 0=-1/2 obstruction; crossed hidden tuples repair feasibility"


def test_shared_profile_cover():
    uniform = matrix([[F(1, 2), F(1, 2)]])
    l1 = Local(matrix([[1]]), uniform)
    l2 = Local(uniform, identity(2))
    problem = Problem((l1, l2), ((0, 0), (0, 1)), ((0, 0), (1, 1)),
                      uniform[0], identity(2), uniform)
    equal(matmul(l1.A, l1.B), matmul(l2.A, l2.B), "same complete local coupling")
    diagonal_obstruction(problem, 0, 0)
    # A stochastic common source exists: its local comparison C2 is not deterministic.
    a, b = matrix([[1]]), uniform
    c1, c2 = matrix([[1]]), uniform
    equal(matmul(a, c1), l1.A, "stochastic common source A1")
    equal(matmul(a, c2), l2.A, "stochastic common source A2")
    equal(matmul(c1, l1.B), b, "stochastic common source B1")
    equal(matmul(c2, l2.B), b, "stochastic common source B2")
    require(all(x not in (ZERO, ONE) for x in c2[0]), "comparison genuinely stochastic")
    return "same coupling; no deterministic cover (0=-1); stochastic common source verified"


def projected_tuple(t, coordinates):
    return tuple(t[i] for i in coordinates)


def restrict(problem, z, coordinates):
    """Push forward a complete retained certificate; Q must descend exactly."""
    e = tuple(sorted({projected_tuple(h, coordinates) for h in problem.E}))
    s = tuple(sorted({projected_tuple(x, coordinates) for x in problem.S}))
    w = tuple(sum((problem.w[k] for k, x in enumerate(problem.S)
                   if projected_tuple(x, coordinates) == y), ZERO) for y in s)
    q = []
    for y in s:
        rows = {problem.Q[k] for k, x in enumerate(problem.S) if projected_tuple(x, coordinates) == y}
        equal(len(rows), 1, "Q descends through coordinate projection")
        q.append(next(iter(rows)))
    target = Problem(tuple(problem.locals[i] for i in coordinates), e, s, w, tuple(q), problem.R)
    zz = {(j, hh, ss): sum((z.get((j, h, x), ZERO) for h in problem.E for x in problem.S
                            if projected_tuple(h, coordinates) == hh
                            and projected_tuple(x, coordinates) == ss), ZERO)
          for j in problem.J for hh in e for ss in s}
    check_certificate(target, zz)
    projection = matrix([[int(projected_tuple(x, coordinates) == y) for y in s] for x in problem.S])
    return target, zz, projection


def posterior_map(full, full_z, smaller, smaller_z, coordinates):
    full_nf, small_nf = normal_form(full, full_z), normal_form(smaller, smaller_z)
    full_a, small_a = check_certificate(full, full_z), check_certificate(smaller, smaller_z)
    chi = matrix([[full_a[j, h] / small_a[jj, hh]
                   if j == jj and projected_tuple(h, coordinates) == hh else ZERO
                   for j, h in full_nf.labels] for jj, hh in small_nf.labels])
    for row in chi:
        equal(sum(row, ZERO), ONE, "posterior map normalized")
    equal(matmul(small_nf.A, chi), full_nf.A, "posterior root equation")
    projection = matrix([[int(projected_tuple(s, coordinates) == ss) for ss in smaller.S] for s in full.S])
    equal(matmul(chi, matmul(full_nf.B, projection)), small_nf.B, "posterior retained-state equation")
    for new_i, old_i in enumerate(coordinates):
        equal(matmul(chi, selector(full_nf.labels, old_i, len(full.locals[old_i].B))),
              selector(small_nf.labels, new_i, len(smaller.locals[new_i].B)),
              "posterior/local-selector compatibility")
    return chi


def three_piece_fixture():
    states = tuple(product(range(2), repeat=3))
    alpha = {(j, h): F(1 + j * len(states) + k, 136)
             for j in range(2) for k, h in enumerate(states)}
    locals_ = tuple(Local(matrix([[sum((alpha[j, h] for h in states if h[i] == u), ZERO)
                                   for u in range(2)] for j in range(2)]), identity(2)) for i in range(3))
    w = tuple(sum((alpha[j, h] for j in range(2)), ZERO) for h in states)
    r = matrix([[sum((alpha[j, h] for h in states), ZERO)] for j in range(2)])
    full = Problem(locals_, states, states, w, matrix([[1] for _ in states]), r)
    z = {(j, h, h): alpha[j, h] for j in full.J for h in states}
    return full, z


def test_three_piece_coherence():
    full, z = three_piece_fixture()
    check_round_trip(full, z)
    pair, pair_z, f32 = restrict(full, z, (0, 1))
    one, one_z, f21 = restrict(pair, pair_z, (0,))
    direct, direct_z, f31 = restrict(full, z, (0,))
    equal(one, direct, "nested restricted datum")
    equal(one_z, direct_z, "nested restricted certificate")
    equal(matmul(f32, f21), f31, "coarse projection associativity")
    chi23 = posterior_map(full, z, pair, pair_z, (0, 1))
    chi12 = posterior_map(pair, pair_z, one, one_z, (0,))
    chi13 = posterior_map(full, z, direct, direct_z, (0,))
    equal(matmul(chi12, chi23), chi13, "posterior-ratio telescoping")
    require(any(0 < x < 1 for row in chi13 for x in row), "posterior test must be nontrivial")
    # Parenthesization changes only tuple packaging if the whole certificate is retained.
    left = {(j, ((h[0], h[1]), h[2]), ((s[0], s[1]), s[2])): v for (j, h, s), v in z.items()}
    right = {(j, (h[0], (h[1], h[2])), (s[0], (s[1], s[2]))): v for (j, h, s), v in z.items()}
    reassociated = {(j, (h[0][0], (h[0][1], h[1])), (s[0][0], (s[0][1], s[1]))): v
                    for (j, h, s), v in left.items()}
    equal(reassociated, right, "retained full-certificate reassociation")
    return "16 positive alpha rows; nested pushforwards, selector squares and posterior telescoping exact"




def channel_transport(problem, z, u, coordinates, local_channels, g):
    """Lawful product-channel fixture constructor with a constant readout.

    The resulting L is generally stochastic, not a coordinate function. The
    actual input squares are checked rather than assumed from this recipe.
    """
    equal(len(u), len(problem.R), "announcement channel source size")
    for row in u:
        equal(sum(row, ZERO), ONE, "announcement channel stochastic")
    for channel in (g,) + tuple(local_channels):
        for row in channel:
            equal(sum(row, ZERO), ONE, "retained/output channel stochastic")
            require(all(x >= 0 for x in row), "channel nonnegative")
    require(all(x >= 0 for row in u for x in row), "announcement channel nonnegative")
    equal(len(set(problem.Q)), 1, "this transport fixture has a constant readout")
    equal(len(coordinates), len(local_channels), "local channel count")
    states = tuple(product(*(range(len(channel[0])) for channel in local_channels)))
    hidden = tuple(sorted({projected_tuple(h, coordinates) for h in problem.E}))
    def coefficient(s, ss):
        value = ONE
        for k, old_i in enumerate(coordinates):
            value *= local_channels[k][s[old_i]][ss[k]]
        return value
    l = matrix([[coefficient(s, ss) for ss in states] for s in problem.S])
    for row in l:
        equal(sum(row, ZERO), ONE, "global retained channel stochastic")
    ut = transpose(u)
    locals_ = tuple(Local(matmul(ut, problem.locals[old_i].A),
                          matmul(problem.locals[old_i].B, local_channels[k]))
                    for k, old_i in enumerate(coordinates))
    qrow = matmul((problem.Q[0],), g)[0]
    target = Problem(locals_, hidden, states, matmul((problem.w,), l)[0],
                     tuple(qrow for _ in states), matmul(matmul(ut, problem.R), g))
    equal(matmul(problem.Q, g), matmul(l, target.Q), "Q G = L Qprime")
    for k, old_i in enumerate(coordinates):
        pi = coordinate_projection(problem.S, old_i, len(problem.locals[old_i].B[0]))
        piprime = coordinate_projection(target.S, k, len(target.locals[k].B[0]))
        equal(matmul(pi, local_channels[k]), matmul(l, piprime), "pi_i L_i = L pi_i prime")
        equal(matmul(problem.locals[old_i].B, local_channels[k]), target.locals[k].B,
              "B_i L_i = B_i prime")
        equal(matmul(ut, problem.locals[old_i].A), target.locals[k].A,
              "U transpose A_i = A_i prime")
    zz = {(jp, hh, ss): sum((u[j][jp] * z.get((j, h, s), ZERO) * l[k][kk]
                            for j in problem.J for h in problem.E
                            if projected_tuple(h, coordinates) == hh
                            for k, s in enumerate(problem.S)), ZERO)
          for jp in target.J for hh in target.E for kk, ss in enumerate(target.S)}
    check_round_trip(target, zz)
    return target, zz, l


def posterior_channel_map(full, z, target, target_z, u, coordinates, l):
    source_nf, target_nf = normal_form(full, z), normal_form(target, target_z)
    alpha, target_alpha = check_certificate(full, z), check_certificate(target, target_z)
    chi = matrix([[u[j][jp] * alpha[j, h] / target_alpha[jp, hh]
                   if projected_tuple(h, coordinates) == hh else ZERO
                   for j, h in source_nf.labels] for jp, hh in target_nf.labels])
    for row in chi:
        equal(sum(row, ZERO), ONE, "randomized posterior normalization")
    transported = Implementation(tuple((j, projected_tuple(h, coordinates)) for j, h in source_nf.labels),
                                 matmul(transpose(u), source_nf.A), matmul(source_nf.B, l))
    check_implementation(target, transported)
    equal(certificate_from_implementation(target, transported), target_z, "Pprime F = Fstar P")
    equal(matmul(target_nf.A, chi), transported.A, "randomized posterior initialization")
    equal(matmul(chi, transported.B), target_nf.B, "randomized posterior B equation")
    for k, old_i in enumerate(coordinates):
        equal(matmul(chi, selector(source_nf.labels, old_i, len(full.locals[old_i].B))),
              selector(target_nf.labels, k, len(target.locals[k].B)), "randomized posterior selector square")
    return chi


def test_randomized_transport_coherence():
    full, z = three_piece_fixture()
    u = matrix([[F(3, 4), F(1, 4)], [F(1, 3), F(2, 3)]])
    uprime = matrix([[F(2, 3), F(1, 3)], [F(1, 4), F(3, 4)]])
    l0 = matrix([[F(4, 5), F(1, 5)], [F(1, 5), F(4, 5)]])
    l1 = matrix([[F(3, 4), F(1, 4)], [F(1, 4), F(3, 4)]])
    lprime = uprime
    g = matrix([[F(1, 3), F(2, 3)]])
    gprime = uprime
    pair, pair_z, l32 = channel_transport(full, z, u, (0, 1), (l0, l1), g)
    one, one_z, l21 = channel_transport(pair, pair_z, uprime, (0,), (lprime,), gprime)
    composite_u, composite_g = matmul(u, uprime), matmul(g, gprime)
    direct, direct_z, l31 = channel_transport(full, z, composite_u, (0,), (matmul(l0, lprime),), composite_g)
    equal(one, direct, "randomized direct/iterated data")
    equal(one_z, direct_z, "randomized direct/iterated tensor")
    equal(matmul(l32, l21), l31, "stochastic retained-channel composition")
    chi23 = posterior_channel_map(full, z, pair, pair_z, u, (0, 1), l32)
    chi12 = posterior_channel_map(pair, pair_z, one, one_z, uprime, (0,), l21)
    chi13 = posterior_channel_map(full, z, direct, direct_z, composite_u, (0,), l31)
    equal(matmul(chi12, chi23), chi13, "randomized posterior telescoping")
    equal(composite_u, matrix([[F(9, 16), F(7, 16)], [F(7, 18), F(11, 18)]]),
          "nontrivial composite announcement channel")
    require(any(0 < x < 1 for row in l31 for x in row), "retained channel genuinely stochastic")
    require(any(0 < x < 1 for row in chi13 for x in row), "posterior genuinely stochastic")
    # A second chain has a zero-probability intermediate announcement. The
    # corresponding normal-form states are omitted; telescoping still holds.
    collapse = matrix([[1, 0], [1, 0]])
    sparse, sparse_z, sparse_l = channel_transport(full, z, collapse, (0, 1), (l0, l1), g)
    sparse_alpha = check_certificate(sparse, sparse_z)
    require(any(value == 0 for value in sparse_alpha.values()), "zero intermediate alpha regression")
    after, after_z, after_l = channel_transport(sparse, sparse_z, uprime, (0,), (lprime,), gprime)
    direct_sparse, direct_sparse_z, direct_sparse_l = channel_transport(
        full, z, matmul(collapse, uprime), (0,), (matmul(l0, lprime),), composite_g)
    equal(after, direct_sparse, "zero-intermediate direct/iterated data")
    equal(after_z, direct_sparse_z, "zero-intermediate direct/iterated tensor")
    first_chi = posterior_channel_map(full, z, sparse, sparse_z, collapse, (0, 1), sparse_l)
    second_chi = posterior_channel_map(sparse, sparse_z, after, after_z, uprime, (0,), after_l)
    direct_chi = posterior_channel_map(full, z, direct_sparse, direct_sparse_z,
                                       matmul(collapse, uprime), (0,), direct_sparse_l)
    equal(matmul(second_chi, first_chi), direct_chi, "telescoping omits zero intermediate alpha")
    return "random U/L/G plus tuple forgetting: input squares, A/B and posterior composition exact, including zero intermediate alpha"

def test_noncanonical_aggregation_and_direction():
    # A genuine noncanonical implementation: one noise state is reached by
    # both announcements, plus one equality/inequality state for each one.
    p, z, _ = correlation_example(2, F(1, 2))
    noise_and_matches = Implementation(
        ((0, (0, 0)), (0, (0, 0)), (1, (0, 0))),
        matrix([[F(1, 4), F(1, 4), 0], [F(1, 4), 0, F(1, 4)]]),
        matrix([[F(1, 4)] * 4, [F(1, 2), 0, 0, F(1, 2)], [0, F(1, 2), F(1, 2), 0]]),
    )
    generated = certificate_from_implementation(p, noise_and_matches)
    equal(generated, z, "noncanonical implementation aggregates to same Z")
    equal(len(normal_form(p, generated).labels), 2, "canonical construction removes redundant state")

    # A directional regression: forgetting a hidden tag averages two distinct
    # correlation profiles. The posterior arrow points from normalized
    # pushforward to pushforward of the normal form, not conversely.
    fair = Local(matrix([[1]]), matrix([[F(1, 2), F(1, 2)]]))
    tag = Local(matrix([[F(1, 2), F(1, 2)]]), matrix([[1], [1]]))
    states = tuple((x, y, 0) for x, y in product(range(2), repeat=2))
    hidden = ((0, 0, 0), (0, 0, 1))
    full = Problem((fair, fair, tag), hidden, states, tuple([F(1, 4)] * 4),
                   matrix([[1]] * 4), matrix([[1]]))
    zz = {(0, h, s): F(1, 4) for h in hidden for s in states if (s[0] != s[1]) == bool(h[2])}
    small, small_z, projection = restrict(full, zz, (0, 1))
    chi = posterior_map(full, zz, small, small_z, (0, 1))
    equal(chi, matrix([[F(1, 2), F(1, 2)]]), "posterior direction fixture")
    full_nf, small_nf = normal_form(full, zz), normal_form(small, small_z)
    equal((len(full_nf.labels), len(small_nf.labels)), (2, 1), "restriction changes canonical state count")
    reverse = matrix([[1], [1]])  # The only normalized matrix of this shape.
    require(matmul(reverse, small_nf.B) != matmul(full_nf.B, projection),
            "reverse arrow must fail retained-profile equation")
    return "shared-announcement source aggregates exactly; posterior 1-to-2 works, reverse 2-to-1 fails"

def test_incompatible_pair_glues():
    bits = tuple(product(range(2), repeat=2))
    fair = Local(matrix([[1]]), matrix([[F(1, 2), F(1, 2)]]))
    for noisy in (False, True):
        favored, other = (F(9, 20), F(1, 20)) if noisy else (F(1, 2), ZERO)
        pairs = []
        for unequal in (False, False, True):
            w = tuple(favored if (a != b) == unequal else other for a, b in bits)
            # In the deterministic limit discard zero-mass coarse cells; in the
            # full-support case retain all four. Zero w is allowed by the validator.
            states = tuple(s for s, value in zip(bits, w) if value > 0)
            positive_w = tuple(value for value in w if value > 0)
            p = Problem((fair, fair), ((0, 0),), states, positive_w,
                        matrix([[1] for _ in states]), matrix([[1]]))
            z = {(0, (0, 0), s): value for s, value in zip(states, positive_w)}
            check_round_trip(p, z)
            pairs.append(dict(zip(bits, w)))
        # Pair constraints AB equal, BC equal, AC opposite cannot all hold.
        scores = {triple: int(triple[0] == triple[1]) + int(triple[1] == triple[2])
                  + int(triple[0] != triple[2]) for triple in product(range(2), repeat=3)}
        equal(max(scores.values()), 2, "pointwise dual bound")
        required = sum((value for (a, b), value in pairs[0].items() if a == b), ZERO)
        required += sum((value for (a, b), value in pairs[1].items() if a == b), ZERO)
        required += sum((value for (a, b), value in pairs[2].items() if a != b), ZERO)
        equal(required, F(27, 10) if noisy else F(3), "pairwise required score")
        require(required > 2, "dual inequality not violated")
    return "all pair certificates feasible; no triple: required score 3 or 27/10 > 2"



def test_umbrella_joint_witness_commitment():
    # A shared retained fair bit and two singleton-hidden local mechanisms.
    # Local output 1 copies the retained bit; output 2 flips it. A diagonal
    # joint output law has the correct separate marginals, but cannot retain
    # both chosen (retained bit, local output) witnesses simultaneously.
    b = matrix([[F(1, 2), F(1, 2)]])
    q1, q2 = identity(2), matrix([[0, 1], [1, 0]])
    local_a = matrix([[1]])
    retained = matmul(local_a, b)[0]
    k1, k2 = matmul(b, q1)[0], matmul(b, q2)[0]
    equal(k1, retained, "first local stochastic link output")
    equal(k2, retained, "second local stochastic link output")
    witness1 = matrix([[retained[t] * q1[t][u] for u in range(2)] for t in range(2)])
    witness2 = matrix([[retained[t] * q2[t][u] for u in range(2)] for t in range(2)])
    desired = matrix([[F(1, 2), 0], [0, F(1, 2)]])
    for u in range(2):
        equal(sum(desired[u], ZERO), k1[u], "desired first output marginal")
        equal(sum((desired[v][u] for v in range(2)), ZERO), k2[u], "desired second output marginal")
        equal(sum(witness1[u], ZERO), retained[u], "first local witness retained marginal")
        equal(sum(witness2[u], ZERO), retained[u], "second local witness retained marginal")
        equal(sum((witness1[t][u] for t in range(2)), ZERO), k1[u], "first local witness output marginal")
        equal(sum((witness2[t][u] for t in range(2)), ZERO), k2[u], "second local witness output marginal")
    atoms = tuple(product(range(2), repeat=3))  # (s, u1, u2)
    allowed_by_local_witnesses = {atom for atom in atoms
                                  if witness1[atom[0]][atom[1]] > 0
                                  and witness2[atom[0]][atom[2]] > 0}
    allowed_by_joint_output = {atom for atom in atoms if desired[atom[1]][atom[2]] > 0}
    equal(allowed_by_local_witnesses, {(0, 0, 1), (1, 1, 0)}, "forced retained-output atoms")
    equal(allowed_by_local_witnesses & allowed_by_joint_output, set(), "empty joint witness support")
    equal(sum((sum(row, ZERO) for row in desired), ZERO), ONE, "desired nonzero mass")
    # Equivalent exact separating inequality, valid on every atom.
    scores = [int(t == u) + int(v == 1 - t) + int(u == v) for t, u, v in atoms]
    equal(max(scores), 2, "umbrella pointwise dual bound")
    required = sum((witness1[t][t] + witness2[t][1 - t] + desired[t][t]
                    for t in range(2)), ZERO)
    equal(required, F(3), "three required probability-one events")
    require(required > max(scores), "umbrella dual obstruction")
    # Observable marginals plus a retained marginal alone are compatible.
    # The independent coupling demonstrates why the extra witness commitment
    # must be explicit: it has those marginals but not either fixed pair law.
    independent = {(t, u, v): retained[t] * desired[u][v] for t, u, v in atoms}
    for t in range(2):
        equal(sum((independent[t, u, v] for u, v in product(range(2), repeat=2)), ZERO),
              retained[t], "ordinary coupling retained marginal")
    for u, v in product(range(2), repeat=2):
        equal(sum((independent[t, u, v] for t in range(2)), ZERO),
              desired[u][v], "ordinary coupling joint output marginal")
    first_pair = matrix([[sum((independent[t, u, v] for v in range(2)), ZERO)
                          for u in range(2)] for t in range(2)])
    second_pair = matrix([[sum((independent[t, u, v] for u in range(2)), ZERO)
                           for v in range(2)] for t in range(2)])
    require(first_pair != witness1 and second_pair != witness2,
            "ordinary coupling must fail the additional pair-witness commitment")
    return "local links and output marginals valid; retained pair witnesses force unequal outputs: 3 > 2"

def expect_failure(fn, label):
    try:
        fn()
    except CheckFailure:
        return
    raise CheckFailure(f"negative control did not fail: {label}")


def test_zero_rows_and_negative_controls():
    states = ((0, 0), (1, 1))
    a = matrix([[F(1, 2), 0], [0, F(1, 2)]])
    local = Local(a, identity(2))
    p = Problem((local, local), states, states, (F(1, 2), F(1, 2)), identity(2), a)
    z = {(0, (0, 0), (0, 0)): F(1, 2), (1, (1, 1), (1, 1)): F(1, 2)}
    alpha = check_certificate(p, z)
    equal(sum(v == 0 for v in alpha.values()), 2, "two zero alpha rows")
    nf = check_round_trip(p, z)
    equal(len(nf.labels), 2, "zero alpha rows omitted before division")
    # The theorem also permits zero announcement/coarse marginals. No
    # conditional row is invented there: all zero-alpha states are omitted.
    states_with_unused = ((0, 0), (1, 1), (2, 2))
    a_with_unused = matrix([[F(1, 2), 0, 0], [0, F(1, 2), 0], [0, 0, 0]])
    local_with_unused = Local(a_with_unused, identity(3))
    unused_problem = Problem((local_with_unused, local_with_unused), states_with_unused,
                             states_with_unused, (F(1, 2), F(1, 2), ZERO), identity(3), a_with_unused)
    unused_alpha = check_certificate(unused_problem, z)
    equal(sum(value == 0 for value in unused_alpha.values()), 7, "zero announcement/coarse alpha rows")
    unused_nf = check_round_trip(unused_problem, z)
    equal(len(unused_nf.labels), 2, "zero announcement/coarse coordinates add no arbitrary conditional state")
    bad = dict(z)
    bad[0, (0, 0), (0, 0)] -= F(1, 10)
    expect_failure(lambda: check_certificate(p, bad), "wrong mass")
    bad_negative = dict(z)
    bad_negative[0, (0, 0), (1, 1)] = -F(1, 10)
    expect_failure(lambda: check_certificate(p, bad_negative), "negative Z")
    bad_forbidden = dict(z)
    bad_forbidden[0, (0, 1), (0, 0)] = ONE
    expect_failure(lambda: check_certificate(p, bad_forbidden), "forbidden hidden tuple")
    expect_failure(lambda: check_equality_obstruction(p, {}), "vacuous obstruction")
    expect_failure(lambda: matrix([[0.5]]), "binary floating-point input")
    return "zero alpha/p/w coordinates omitted safely; five invalid-certificate/inexact-input controls rejected"


def main():
    tests = (
        ("split necessity and exact rank lower bounds", test_correlation_family),
        ("Boolean/stochastic separation", test_boolean_mismatch),
        ("equal observable law is not a deterministic common cover", test_shared_profile_cover),
        ("three-piece retained-certificate coherence", test_three_piece_coherence),
        ("randomized interface transport coherence", test_randomized_transport_coherence),
        ("noncanonical aggregation and posterior direction", test_noncanonical_aggregation_and_direction),
        ("independent pairwise glues need not extend", test_incompatible_pair_glues),
        ("umbrella joint-witness commitment is additional structure", test_umbrella_joint_witness_commitment),
        ("zero rows and negative controls", test_zero_rows_and_negative_controls),
    )
    print("Exact rational joint-gluing checks (stdlib fractions; no assert-only tests)")
    for label, test in tests:
        detail = test()
        print(f"PASS | {label}\n       {detail}")
    print(f"ALL {len(tests)} CHECK GROUPS PASSED")


if __name__ == "__main__":
    main()
