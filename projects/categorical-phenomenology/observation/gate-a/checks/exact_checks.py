#!/usr/bin/env python3
"""Independent finite Gate A checks; exact stdlib arithmetic, NOT a proof.

Run: python3 exact_checks.py --output results.json
No SymPy, NumPy, network, randomness, assert statements, or floating point.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb, gcd
from functools import reduce
from pathlib import Path
import argparse
import json
import sys


class CheckFailure(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise CheckFailure(message)


def equal(actual, expected, message):
    require(actual == expected, f"{message}: got {actual!r}; expected {expected!r}")


def zero(n):
    return tuple(tuple(0 for _ in range(n)) for _ in range(n))


def identity(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def diagonal(values):
    return tuple(tuple(v if i == j else 0 for j in range(len(values)))
                 for i, v in enumerate(values))


def sym(n, i, j):
    return tuple(tuple(int((a, b) in ((i, j), (j, i))) for b in range(n))
                 for a in range(n))


def add(A, B):
    return tuple(tuple(a + b for a, b in zip(ar, br)) for ar, br in zip(A, B))


def scale(c, A):
    return tuple(tuple(c * v for v in row) for row in A)


def multiply(A, B):
    return tuple(tuple(sum(a * b for a, b in zip(row, col)) for col in zip(*B))
                 for row in A)


def transpose(A):
    return tuple(zip(*A))


def congruence(L, Q):
    return multiply(multiply(L, Q), transpose(L))


def anticommutator(S, Q):
    return add(multiply(S, Q), multiply(Q, S))


def row_multiply(row, M):
    return tuple(sum(a * b for a, b in zip(row, col)) for col in zip(*M))


def dot(row, col):
    return sum(a * b for a, b in zip(row, col))


def symmetric_coordinates(Q):
    n = len(Q)
    return tuple(Q[i][j] for i in range(n) for j in range(i, n))


def symmetric_basis(n):
    return [sym(n, i, j) for i in range(n) for j in range(i, n)]


def primitive(Q):
    """Integer scaling leaves the span unchanged and controls coefficient size."""
    values = [v for row in Q for v in row]
    require(all(isinstance(v, int) for v in values), 'primitive needs integers')
    divisor = reduce(gcd, (abs(v) for v in values), 0)
    return tuple(tuple(v // divisor for v in row) for row in Q) if divisor else Q


class RationalSpan:
    """Incremental exact echelon reduction; original vectors are never overwritten."""
    def __init__(self):
        self.rows = {}

    def insert(self, values):
        v = list(map(F, values))
        for pivot, row in sorted(self.rows.items()):
            c = v[pivot]
            if c:
                v = [a - c * b for a, b in zip(v, row)]
        pivot = next((i for i, value in enumerate(v) if value), None)
        if pivot is None:
            return False
        c = v[pivot]
        self.rows[pivot] = tuple(value / c for value in v)
        return True

    def __len__(self):
        return len(self.rows)


def rank(M):
    span = RationalSpan()
    for row in M:
        span.insert(row)
    return len(span)


def inverse(M):
    n = len(M)
    rows = [list(map(F, row)) + list(Irow) for row, Irow in zip(M, identity(n))]
    for j in range(n):
        pivot = next((i for i in range(j, n) if rows[i][j]), None)
        require(pivot is not None, 'matrix is singular')
        rows[j], rows[pivot] = rows[pivot], rows[j]
        c = rows[j][j]
        rows[j] = [v / c for v in rows[j]]
        for i in range(n):
            if i != j:
                c = rows[i][j]
                rows[i] = [a - c * b for a, b in zip(rows[i], rows[j])]
    return tuple(tuple(row[n:]) for row in rows)


def closure(n, edges, seeds, regime):
    """BFS spans all words, terminating at invariance. Pullbacks use integer scales."""
    S = [sym(n, *edge) for edge in edges]
    if regime == 'jet':
        operators = [('jet', matrix) for matrix in S]
    elif regime == 'flow_log2':
        # exp(-log(2) S) = I + S^2/4 - 3S/4; numerator is 4L.
        operators = [('step', add(add(scale(4, identity(n)), multiply(matrix, matrix)),
                                  scale(-3, matrix))) for matrix in S]
    else:
        steps = (F(1, 3), F(2, 3)) if regime == 'gd_two_steps' else (F(1, 3),)
        operators = [('step', add(scale(step.denominator, identity(n)),
                                  scale(-step.numerator, matrix)))
                     for matrix in S for step in steps]
    span = RationalSpan()
    basis = []
    depths = []
    for seed in seeds:
        Q = sym(n, *seed)
        if span.insert(symmetric_coordinates(Q)):
            basis.append(Q)
            depths.append(0)
    cursor = 0
    while cursor < len(basis):
        Q, depth = basis[cursor], depths[cursor]
        for kind, operator in operators:
            candidate = primitive(anticommutator(operator, Q) if kind == 'jet'
                                  else congruence(operator, Q))
            if span.insert(symmetric_coordinates(candidate)):
                basis.append(candidate)
                depths.append(depth + 1)
        cursor += 1
    D = n * (n + 1) // 2
    require(len(basis) <= D, 'closure cannot exceed ambient dimension')
    first_far = next((d for Q, d in zip(basis, depths) if Q[-1][-1]), None)
    return {'dimension': len(span), 'max_basis_depth': max(depths),
            'first_far_diagonal_depth': first_far,
            'dimensions_through_depth': [sum(d <= level for d in depths)
                                         for level in range(max(depths) + 1)]}, basis


def graph_checks():
    records = []
    cases = []
    for n in range(2, 9):
        cases.append(('path', n, [(i, i + 1) for i in range(n - 1)]))
    for n in range(3, 7):
        cases.append(('star', n, [(0, j) for j in range(1, n)]))
    for n in (4, 6):
        cases.append(('even_cycle', n, [(i, i + 1) for i in range(n - 1)] + [(0, n - 1)]))
    cases.append(('complete_bipartite_2_3', 5, [(i, j) for i in range(2) for j in range(2, 5)]))
    for name, n, edges in cases:
        for regime in ('jet', 'flow_log2', 'gd_two_steps', 'gd_fixed_1_3'):
            if n >= 7 and regime != 'jet':
                continue
            result, basis = closure(n, edges, [edges[0]], regime)
            expected = n * (n + 1) // 2 - int(regime in ('jet', 'flow_log2') or n == 2)
            label = f'{name} n={n} {regime}'
            equal(result['dimension'], expected, label + ' observation dimension')
            if name == 'path' and regime == 'jet':
                equal(result['max_basis_depth'], 2 * n - 3, label + ' sharp jet depth')
                equal(result['first_far_diagonal_depth'], 2 * n - 3,
                      label + ' first far diagonal')
            if regime != 'jet':
                require(result['max_basis_depth'] <= expected - 1, label + ' endpoint word bound')
            # Directly compute the supplied bipartition, not an assumed alternating labelling.
            signs = {0: 1}
            while len(signs) < n:
                old = len(signs)
                for i, j in edges:
                    if i in signs:
                        if j in signs:
                            equal(signs[j], -signs[i], label + ' bipartite consistency')
                        signs[j] = -signs[i]
                    elif j in signs:
                        signs[i] = -signs[j]
                require(len(signs) > old, label + ' connectedness')
            if regime in ('jet', 'flow_log2'):
                require(all(sum(Q[i][i] * signs[i] for i in range(n)) == 0 for Q in basis),
                        label + ' annihilation of signed diagonal')
            records.append({'graph': name, 'vertices': n, 'regime': regime, **result})
    # A 3-vertex path, a separate edge, and one isolated vertex: cross blocks invisible.
    for regime, expected in [('jet', 7), ('flow_log2', 7),
                             ('gd_two_steps', 8), ('gd_fixed_1_3', 8)]:
        result, basis = closure(6, [(0, 1), (1, 2), (3, 4)], [(0, 1), (3, 4)], regime)
        equal(result['dimension'], expected, 'disconnected ' + regime)
        require(all(Q[5][j] == 0 for Q in basis for j in range(6)), 'isolated vertex invisible')
        require(all(Q[i][j] == 0 for Q in basis for i in (0, 1, 2) for j in (3, 4)),
                'cross-component blocks invisible')
        records.append({'graph': 'path3_plus_edge_plus_isolate', 'vertices': 6,
                        'regime': regime, **result})
    return records


def polynomial_on_operator(P, Q, roots, values):
    """Evaluate the exact Lagrange interpolating polynomial without symbolic software."""
    out = zero(len(Q))
    for i, (root, value) in enumerate(zip(roots, values)):
        term = Q
        denominator = F(1)
        for j, other in enumerate(roots):
            if i != j:
                term = add(P(term), scale(-other, term))
                denominator *= root - other
        out = add(out, scale(value / denominator, term))
    return out


def fixed_step_checks():
    results = []
    S = sym(3, 0, 1)
    J = diagonal((1, -1, 1))
    for eta in (F(1, 5), F(1, 3), F(1, 2), F(2, 3), F(4, 5)):
        L = add(identity(3), scale(-eta, S))
        roots = ((1 - eta)**2, 1 - eta, 1 - eta**2, F(1), 1 + eta, (1 + eta)**2)
        equal(len(set(roots)), 6, 'fixed-step interpolation nodes distinct')
        P = lambda Q: congruence(L, Q)
        for Q in symmetric_basis(3):
            equal(polynomial_on_operator(P, Q, roots, tuple(map(F, (2, 1, 0, 0, -1, -2)))),
                  anticommutator(S, Q), f'fixed-step interpolation eta={eta}')
        # Two-step polarization identities, including all symmetric coordinates.
        L2 = add(identity(3), scale(-2 * eta, S))
        for Q in symmetric_basis(3):
            recovered_T = scale(1 / (2 * eta), add(add(congruence(L2, Q), scale(-4, P(Q))), scale(3, Q)))
            equal(recovered_T, anticommutator(S, Q), 'two-size T identity')
            recovered_R = scale(1 / (2 * eta**2), add(add(congruence(L2, Q), scale(-2, P(Q))), Q))
            equal(recovered_R, multiply(multiply(S, Q), S), 'two-size R identity')
        results.append({'eta': str(eta), 'interpolation_verified_on_Sym3_basis': True})
    for eta in (F(1, 3), F(1, 2), F(2, 3)):
        L = add(identity(2), scale(-eta, sym(2, 0, 1)))
        equal(congruence(L, diagonal((1, -1))), scale(1 - eta**2, diagonal((1, -1))),
              'dimension-2 GD invisible line')
    flow_L = add(add(identity(3), scale(F(1, 4), multiply(S, S))), scale(F(-3, 4), S))
    equal(congruence(flow_L, J), J, 'sampled flow preserves J exactly')
    for Q in symmetric_basis(3):
        equal(polynomial_on_operator(lambda X: congruence(flow_L, X), Q,
                                     (F(4), F(2), F(1), F(1, 2), F(1, 4)),
                                     tuple(map(F, (-2, -1, 0, 1, 2)))),
              anticommutator(S, Q), 'fixed-duration flow interpolation')
    return results


def width_and_descent_checks():
    stars = []
    for n in range(3, 13):
        J = diagonal((1,) + (-1,) * (n - 1))
        full = identity(n)
        thin = add(full, J)
        equal(rank(full), n, 'full native width')
        equal(rank(thin), 1, 'thin native width')
        equal([thin[i][i] for i in range(n)], [2] + [0] * (n - 1), 'thin PSD')
        sensor_S = sym(n, 0, 1)
        derivative_Q = anticommutator(sensor_S, sensor_S)
        require(sum(derivative_Q[i][j] * thin[j][i] for i in range(n) for j in range(n)) != 0,
                'thin flow law differs from zero law, so width zero cannot realize it')
        for c in (F(-1), F(-1, 2), F(0), F(1, 2), F(1)):
            pencil = add(full, scale(c, J))
            require(all(pencil[i][i] >= 0 for i in range(n)), 'PSD pencil sample')
            equal(rank(pencil), (n - 1 if c == -1 else 1 if c == 1 else n), 'pencil rank sample')
        # Pencil PSD iff -1<=c<=1 follows here from its diagonal entries 1+c,1-c.
        stars.append({'vertices': n, 'GD_width_I': n, 'GD_width_I_plus_J': 1,
                      'flow_pencil_min_width': 1})
    witnesses = []
    J = diagonal((1, -1, 1))
    for eta in (F(1, 5), F(1, 3), F(2, 5)):
        for c in (F(-1), F(1, 2)):
            L23 = add(identity(3), scale(-eta, sym(3, 1, 2)))
            L12 = add(identity(3), scale(-eta, sym(3, 0, 1)))
            delta = congruence(L12, congruence(L23, scale(c, J)))
            equal(delta[0][1], -c * eta**3, 'GD non-descent sensor discriminator')
            require(delta[0][1] != 0, 'GD witnesses must distinguish')
            witnesses.append({'eta': str(eta), 'c': str(c), 'observed_difference': str(delta[0][1])})
    # Star sensor 01, control 02 followed by 01: sign changes with bipartition.
    Jstar = diagonal((1, -1, -1))
    eta = F(1, 3)
    L02 = add(identity(3), scale(-eta, sym(3, 0, 2)))
    L01 = add(identity(3), scale(-eta, sym(3, 0, 1)))
    equal(congruence(L01, congruence(L02, Jstar))[0][1], eta**3, 'star GD width witness')
    return {'stars': stars, 'path_non_descent_witnesses': witnesses,
            'dimension_2_exception': {
                'rank_I2': rank(identity(2)), 'rank_diag_2_0': rank(diagonal((2, 0))),
                'same_flow_response': True, 'same_GD_response': True,
                'minimum_compatible_native_width_in_both_regimes': 1,
                'warning': 'For d=2, the GD response state is NOT the full Gram; rank of an arbitrary representative is not its response-minimum width.'},
            'star_sensor_difference_eta_1_3': '1/27'}


def normalize(row):
    total = sum(row)
    require(total > 0, 'zero-probability history encountered')
    return tuple(v / total for v in row)


def reset_matrix(b, q):
    return tuple(tuple(v * w for w in q) for v in b)


def probability_control(events):
    require(all(value >= 0 for M in events for row in M for value in row),
            'negative event probability')
    n = len(events[0])
    equal([sum(sum(M[i]) for M in events) for i in range(n)], [1] * n,
          'control outcome sum row stochastic')


def belief_layers(alpha, events, horizon):
    frontier = {tuple(alpha)}
    seen = set(frontier)
    result = [(set(frontier), set(seen))]
    for _ in range(horizon):
        frontier = {normalize(row_multiply(belief, M)) for belief in frontier for M in events}
        seen |= frontier
        result.append((set(frontier), set(seen)))
    return result


def prime_valuations(value):
    values = {}
    for number, sign in ((value.numerator, 1), (value.denominator, -1)):
        p = 2
        while p * p <= number:
            while number % p == 0:
                values[p] = values.get(p, 0) + sign
                number //= p
            p += 1
        if number > 1:
            values[number] = values.get(number, 0) + sign
    return {p: e for p, e in values.items() if e}


def multiplicative_rank(ratios):
    valuations = [prime_valuations(F(ratio)) for ratio in ratios]
    primes = sorted({p for row in valuations for p in row})
    return rank([[row.get(p, 0) for p in primes] for row in valuations])


def hmm_checks():
    q = (F(1, 2), F(1, 2))
    primes = (2, 3, 5, 7)
    growth = []
    for m in range(1, 5):
        events = []
        for p in primes[:m]:
            A = diagonal((F(1, 2), F(1, 2 * p)))
            R = reset_matrix((F(1, 2), 1 - F(1, 2 * p)), q)
            probability_control((A, R))
            equal(rank(R), 1, 'reset rank one')
            require(all(v > 0 for row in R for v in row), 'reset full support')
            events.extend((A, R))
        equal(multiplicative_rank(primes[:m]), m, 'arithmetic rank of prime generators')
        counts = []
        for n, (_, states) in enumerate(belief_layers(q, events, 8)):
            equal(len(states), comb(n + m, m), f'prime-family m={m}, n={n}')
            counts.append(len(states))
        growth.append({'controls': m, 'degree': m, 'counts_n_0_through_8': counts})
    # Removing whole controls is tested by each prefix m=1,2,3,4 above.
    S = ((F(0), F(1, 8)), (F(1, 2), F(0)))
    reset_q = (F(1, 3), F(2, 3))
    R = reset_matrix((F(7, 8), F(1, 2)), reset_q)
    probability_control((S, R))
    equal(multiply(S, S), scale(F(1, 16), identity(2)), 'finite monomial projective order')
    eigen_q = (F(2, 3), F(1, 3))
    equal(row_multiply(eigen_q, S), tuple(F(1, 4) * v for v in eigen_q), 'common fixed projective point')
    finite_layers = belief_layers(q, (S, R), 8)
    equal({b[0] / b[1] for b in finite_layers[-1][1]}, {F(1), F(4), F(1, 2), F(8)},
          'four-state predictive orbit')
    M0 = diagonal((F(1, 2), F(1, 3)))
    M1 = diagonal((F(1, 2), F(2, 3)))
    probability_control((M0, M1))
    equal(multiplicative_rank((F(3, 2), F(3, 4))), 2, 'mixture arithmetic rank')
    mixture = []
    for n, (exact, at_most) in enumerate(belief_layers(q, (M0, M1), 10)):
        equal(len(exact), n + 1, 'exact-time mixture count')
        equal(len(at_most), comb(n + 2, 2), 'at-most mixture count')
        mixture.append({'n': n, 'exact_time': len(exact), 'at_most': len(at_most)})
    # These terminal effects and their complements are bounded and normalized.
    terminal_tests = (((F(0), F(1, 2)), (F(1), F(1, 2))),
                      ((F(1, 2), F(0)), (F(1, 2), F(1))))
    for test in terminal_tests:
        equal(tuple(sum(effect[i] for effect in test) for i in range(2)), (1, 1),
              'terminal test normalization')
        require(all(0 <= v <= 1 for effect in test for v in effect), 'bounded terminal effects')
    preparation = ((F(1, 2), F(1, 2)), (F(1, 3), F(2, 3)))
    equal(rank(preparation), 2, 'full-support preparation rank')
    for event in (S, R, M0, M1):
        B = multiply(preparation, event)
        equal(multiply(inverse(preparation), B), event, 'response block operator reconstruction')
    # Boundary seed invalidates full-support lower bound, despite rank-two other preparations.
    boundary = (F(1), F(0))
    equal(len(belief_layers(boundary, (M0, M1), 10)[-1][1]), 1,
          'boundary support failure control')
    return {'prime_family': growth,
            'finite_four_state_example': {'counts_n_0_through_8': [len(s) for _, s in finite_layers],
                                          'odds': ['1/2', '1', '4', '8'],
                                          'common_eigenvector': ['2/3', '1/3']},
            'exact_time_vs_at_most': mixture,
            'response_block_reconstruction': True,
            'boundary_seed_count': 1}


def terminal_effect_gap_check():
    """A diagnostic counterexample, not an expected theorem success."""
    preparations = ((F(2, 5), F(3, 5)), (F(3, 5), F(2, 5)))
    effects = ((F(3, 2), F(0)), (F(0), F(3, 2)))
    table = tuple(tuple(dot(p, e) for e in effects) for p in preparations)
    equal(table, ((F(3, 5), F(9, 10)), (F(9, 10), F(3, 5))), 'terminal counterexample table')
    equal(rank(table), 2, 'terminal counterexample observed rank')
    require(all(0 <= value <= 1 for row in table for value in row), 'observed terminal probabilities valid')
    probability_control((identity(2),))
    # Positivity of only the displayed effects defines the ordinary positive quadrant.
    displayed_vertices = ((F(1), F(0)), (F(0), F(1)))
    bad_vertex_values = [dot(v, effect) for v in displayed_vertices for effect in effects]
    equal(max(bad_vertex_values), F(3, 2), 'computed simplex terminal overflow')
    require(max(bad_vertex_values) > 1, 'missing terminal upper bound must be detected')
    complements = tuple(tuple(1 - v for v in effect) for effect in effects)
    repaired_vertices = ((F(1, 3), F(2, 3)), (F(2, 3), F(1, 3)))
    require(all(0 <= dot(v, effect) <= 1 for v in repaired_vertices for effect in effects + complements),
            'complement repair bounds all terminal events')
    return {'status': 'DISPLAYED_HYPOTHESES_GAP_CONFIRMED',
            'observed_rank': 2, 'observed_table': [[str(v) for v in row] for row in table],
            'maximum_terminal_value_at_original_simplex_vertices': '3/2',
            'repair': 'Include every terminal-test complement, or check ell_t <= u on the computed cone and test-outcome normalization.',
            'repaired_vertex_first_coordinates': ['1/3', '2/3'],
            'scope': 'Invalidates displayed simplex realization claim under omitted complements, not existence of any positive realization.'}


def linear_algebra_self_checks():
    equal(rank(((1, 2, 3), (2, 4, 6), (0, 1, 1))), 2, 'rank routine self-test')
    equal(multiply(((1, 2), (3, 5)), inverse(((1, 2), (3, 5)))), identity(2), 'inverse routine self-test')
    equal(multiplicative_rank((F(2), F(4), F(8))), 1, 'dependent multiplicative generators')
    equal(multiplicative_rank((F(3, 2), F(3, 4))), 2, 'independent multiplicative generators')
    try:
        require(False, 'deliberate failure')
    except CheckFailure:
        pass
    else:
        raise CheckFailure('explicit check failure was disabled')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--self-test-failure', action='store_true', help='deliberately fail, including under python -O')
    args = parser.parse_args()
    if args.self_test_failure:
        require(False, 'deliberate failure demonstrates active validation under optimization')
    linear_algebra_self_checks()
    result = {'status': 'PASS_WITH_DIAGNOSTIC_COUNTEREXAMPLE',
              'scope': 'Finite exact checks, not a general proof, novelty clearance, noise analysis, or empirical experiment.',
              'arithmetic': 'Python standard library int and fractions.Fraction only; explicit checks remain active under -O.',
              'graph_closures': graph_checks(),
              'fixed_step_identities': fixed_step_checks(),
              'native_width_and_non_descent': width_and_descent_checks(),
              'hmm_examples': hmm_checks(),
              'comparative_terminal_effect_gap': terminal_effect_gap_check()}
    encoded = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    try:
        main()
    except CheckFailure as exc:
        print(f'CHECK FAILED: {exc}', file=sys.stderr)
        sys.exit(1)
