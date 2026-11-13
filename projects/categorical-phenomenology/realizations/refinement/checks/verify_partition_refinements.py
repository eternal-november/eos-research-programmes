#!/usr/bin/env python3
"""Exact checks of the partition refinement family; Python standard library only.

Construction verification and support-obstruction certificates are exhaustive
for the declared finite roster. Optimality and arbitrary-state impossibility
are mathematical theorems in the report, not results of latent-state search.
"""
from fractions import Fraction as Q
from itertools import product
import hashlib
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def partitions(n):
    if n == 0:
        yield ()
        return
    for p in partitions(n - 1):
        yield p + ((n - 1,),)
        for j in range(len(p)):
            yield p[:j] + (p[j] + (n - 1,),) + p[j + 1:]


def zero(r, c):
    return [[Q(0) for _ in range(c)] for _ in range(r)]


def identity(n):
    a = zero(n, n)
    for i in range(n):
        a[i][i] = Q(1)
    return a


def mm(a, b):
    require(bool(a) and bool(b) and len(a[0]) == len(b), 'matrix dimensions')
    c = zero(len(a), len(b[0]))
    for i, row in enumerate(a):
        for j, x in enumerate(row):
            if x:
                for k, y in enumerate(b[j]):
                    if y:
                        c[i][k] += x * y
    return c


def add(a, b):
    return [[x + y for x, y in zip(r, s)] for r, s in zip(a, b)]


def vm(v, a):
    return mm([v], a)[0]


def probability(v):
    return sum(v, Q(0))


def mass(block, p):
    return sum((p[i] for i in block), Q(0))


def root_vector(n):
    return [Q(1)] + [Q(0)] * (n - 1)


def kernel_valid(kernels):
    size = len(next(iter(kernels.values())))
    total = zero(size, size)
    for a in kernels.values():
        require(len(a) == size and all(len(row) == size for row in a), 'square kernel')
        require(all(x >= 0 for row in a for x in row), 'nonnegative kernel')
        total = add(total, a)
    require(all(sum(row) == 1 for row in total), 'combined transition stochastic')


def coarse_model(B, p):
    n, k = len(p), len(B) + 2
    K = {'a': zero(k, k), '#': zero(k, k)}
    K.update({'b%d' % i: zero(k, k) for i in range(n)})
    for j, block in enumerate(B, 1):
        pb = mass(block, p)
        K['a'][0][j] = pb
        for i in block:
            K['b%d' % i][j][-1] = p[i] / pb
    K['#'][-1][-1] = Q(1)
    kernel_valid(K)
    return K


def fine_model(B, D, p, deterministic):
    blocks = B if deterministic else D
    n, k, m = len(p), len(blocks) + 2, len(B) + 2
    K = {'r%d' % j: zero(k, k) for j in range(len(D))}
    K.update({'b%d' % i: zero(k, k) for i in range(n)})
    K['#'] = zero(k, k)
    L = zero(k, m)
    L[0][0] = L[-1][-1] = Q(1)
    for row, block in enumerate(blocks, 1):
        d = next(j for j, target in enumerate(D) if set(block) <= set(target))
        pb = mass(block, p)
        K['r%d' % d][0][row] = pb
        for i in block:
            K['b%d' % i][row][-1] = p[i] / pb
        if deterministic:
            L[row][row] = Q(1)
        else:
            for j, small in enumerate(B, 1):
                if set(small) <= set(block):
                    L[row][j] = mass(small, p) / pb
    K['#'][-1][-1] = Q(1)
    kernel_valid(K)
    require(all(all(x >= 0 for x in row) and sum(row) == 1 for row in L), 'link stochastic')
    if deterministic:
        require(all(sum(x == 1 for x in row) == 1 and all(x in (0, 1) for x in row) for row in L), 'link deterministic')
    return K, L


def check_witness(B, D, p, deterministic):
    Y = coarse_model(B, p)
    X, L = fine_model(B, D, p, deterministic)
    k, m = len(L), len(L[0])
    alpha = root_vector(k)
    require(vm(alpha, L) == root_vector(m), 'initial link equality')
    for c, kernel in Y.items():
        aggregate = zero(k, k)
        for z, fine_kernel in X.items():
            if ('a' if z.startswith('r') else z) == c:
                aggregate = add(aggregate, fine_kernel)
        require(mm(aggregate, L) == mm(L, kernel), 'joint output-next-state intertwining')
    # Full target law is determined by these two-step probabilities and the
    # exact absorbing terminal state reached after every possible second output.
    for z in X:
        first = vm(alpha, X[z])
        if not z.startswith('r'):
            require(probability(first) == 0, 'no wrong first-phase output')
            continue
        d = int(z[1:])
        require(probability(first) == mass(D[d], p), 'revelation probability')
        for w in X:
            second = vm(first, X[w])
            expected = p[int(w[1:])] if w.startswith('b') and int(w[1:]) in D[d] else Q(0)
            require(probability(second) == expected, 'two-step word probability')
            require(all(x == 0 for x in second[:-1]), 'post-second state is terminal')
            require(vm(second, X['#']) == second, 'all further terminal outputs')
    expected_size = len(B if deterministic else D) + 2
    require(k == expected_size, 'constructed resource cost')
    return k


def obstruction_certificate(B, D, p):
    crossing = [block for block in B if not any(set(block) <= set(d) for d in D)]
    require(bool(crossing), 'obstruction has a crossing coarse block')
    allowed = [[j for j, block in enumerate(B) if set(block) <= set(d)] for d in D]
    missing = [j for j in range(len(B)) if all(j not in js for js in allowed)]
    require(missing and all(B[j] in crossing for j in missing), 'posterior supports cannot cover crossing block')
    missing_mass = sum((mass(B[j], p) for j in missing), Q(0))
    require(missing_mass > 0, 'missing coarse block has positive required initial mass')
    for j in missing:
        for d in D:
            require(any(p[i] > 0 and i not in d for i in B[j]), 'every fine revelation forbids some positive emission of crossing block')
    return missing_mass


def check_polytope_bridge(B, D, p):
    """Explicit K feasibility and disjoint-support exact rank certificate."""
    K = [[mass(b, p) if set(b) <= set(d) else Q(0) for b in B] for d in D]
    emission = [[p[i] / mass(b, p) if i in b else Q(0) for i in range(len(p))] for b in B]
    joint = [[p[i] if i in d else Q(0) for i in range(len(p))] for d in D]
    require(mm(K, emission) == joint, 'polytope K Q = R')
    require([sum(K[r][c] for r in range(len(D))) for c in range(len(B))] ==
            [mass(b, p) for b in B], 'polytope prescribed column masses')
    require([sum(row) for row in K] == [mass(d, p) for d in D], 'polytope row masses')
    supports = [{c for c, x in enumerate(row) if x > 0} for row in K]
    require(all(supports), 'each K row is nonzero')
    require(all(not (supports[r] & supports[s]) for r in range(len(D)) for s in range(r)),
            'pairwise disjoint nonzero K rows certify rank |D|')
    require(mm(identity(len(D)), K) == K, 'nonnegative rank upper witness I K')
    # Disjoint nonzero rows imply ordinary rank |D|; ordinary rank <=
    # nonnegative rank <= |D| gives equality. This is not a rank search.


def binary_noisy_controls():
    emission = [[Q(4, 5), Q(1, 5)], [Q(1, 5), Q(4, 5)]]
    inverse = [[Q(4, 3), -Q(1, 3)], [-Q(1, 3), Q(4, 3)]]
    require(mm(emission, inverse) == identity(2) and mm(inverse, emission) == identity(2),
            'invertible noisy channel implies unique K = R Q^-1')
    specifications = [
        ('independent', Q(1, 4), Q(1, 4), Q(1, 4), Q(1, 4), 1),
        ('intermediate', Q(37, 100), Q(13, 100), Q(9, 20), Q(1, 20), 2),
        ('too_sharp', Q(9, 20), Q(1, 20), Q(7, 12), -Q(1, 12), None)]
    output = {}
    for name, rdiag, roff, kdiag, koff, rank in specifications:
        R = [[rdiag, roff], [roff, rdiag]]
        K = mm(R, inverse)
        require(K == [[kdiag, koff], [koff, kdiag]], 'unique binary solution')
        require(mm(K, emission) == R, 'binary K Q = R')
        require(all(sum(row) == Q(1, 2) for row in K), 'binary row marginal')
        require(all(sum(K[r][c] for r in range(2)) == Q(1, 2) for c in range(2)),
                'binary column marginal')
        require(all(x > 0 for row in R for x in row) and
                all(x > 0 for row in emission for x in row), 'full-support quantitative control')
        if rank is None:
            require(any(x < 0 for row in K for x in row), 'unique solution not nonnegative')
            output[name] = {'feasible': False, 'unique_K': [[str(x) for x in row] for row in K]}
        else:
            require(all(x >= 0 for row in K for x in row), 'feasible binary K')
            determinant = K[0][0]*K[1][1] - K[0][1]*K[1][0]
            require((determinant == 0) == (rank == 1), 'ordinary binary rank')
            if rank == 1:
                require(mm([[Q(1, 2)], [Q(1, 2)]], [[Q(1, 2), Q(1, 2)]]) == K,
                        'rank-one nonnegative factorization')
            else:
                require(mm(identity(2), K) == K, 'rank-two nonnegative factorization')
            output[name] = {'feasible': True, 'nonnegative_rank': rank,
                            'stochastic_states': rank + 2, 'deterministic_states': 4,
                            'unique_K': [[str(x) for x in row] for row in K]}
    return output


def main():
    totals = {'partition_probability_cases': 0, 'feasible_cases': 0,
              'infeasible_support_certificates': 0, 'stochastic_witnesses': 0,
              'deterministic_witnesses': 0, 'strict_resource_gap_cases': 0}
    rows = []
    digest = hashlib.sha256()
    for n in range(1, 6):
        ps = sorted(partitions(n))
        require(len(ps) == len(set(ps)), 'partition enumeration unique')
        require(len(ps) == (1, 2, 5, 15, 52)[n - 1], 'Bell-number roster cardinality')
        weights = [tuple(Q(1, n) for _ in range(n))]
        tilted = tuple(Q(i + 1, n * (n + 1) // 2) for i in range(n))
        if tilted not in weights:
            weights.append(tilted)
        local = {'symbols': n, 'partitions': len(ps), 'probability_vectors': len(weights),
                 'cases': 0, 'feasible': 0, 'infeasible': 0, 'strict_resource_gaps': 0}
        for B, D, p in product(ps, ps, weights):
            require(all(x > 0 for x in p) and sum(p) == 1, 'positive normalized probabilities')
            refines = all(any(set(b) <= set(d) for d in D) for b in B)
            local['cases'] += 1
            totals['partition_probability_cases'] += 1
            if refines:
                check_polytope_bridge(B, D, p)
                scost = check_witness(B, D, p, False)
                dcost = check_witness(B, D, p, True)
                require(scost <= dcost, 'refinement block-count ordering')
                local['feasible'] += 1
                totals['feasible_cases'] += 1
                totals['stochastic_witnesses'] += 1
                totals['deterministic_witnesses'] += 1
                if scost < dcost:
                    local['strict_resource_gaps'] += 1
                    totals['strict_resource_gap_cases'] += 1
                record = (B, D, tuple(map(str, p)), 'positive', scost, dcost)
            else:
                missing = obstruction_certificate(B, D, p)
                local['infeasible'] += 1
                totals['infeasible_support_certificates'] += 1
                record = (B, D, tuple(map(str, p)), 'negative', str(missing))
            digest.update((repr(record) + '\n').encode())
        rows.append(local)
    # Explicit delayed-coin and strict-cost controls.
    fine = ((0,), (1,))
    coarse = ((0, 1),)
    p = (Q(1, 2), Q(1, 2))
    require(obstruction_certificate(coarse, fine, p) == 1, 'late coin cannot reveal future outcome')
    require(check_witness(fine, fine, p, False) == 4, 'early coin supports revelation')
    require(check_witness(fine, coarse, p, False) == 3, 'stochastic comparison compresses internal distinction')
    require(check_witness(fine, coarse, p, True) == 4, 'deterministic comparison retains internal distinction')
    result = {'binary_noisy_controls': binary_noisy_controls(), 'status': 'pass', 'arithmetic': 'exact rational', 'totals': totals,
              'polytope_bridge_positive_certificates': totals['feasible_cases'],
              'roster_by_size': rows, 'case_digest_sha256': digest.hexdigest(),
              'controls': {'late_coin_full_revelation': 'support obstruction',
                           'early_coin_full_revelation_states': 4,
                           'early_coin_no_revelation_stochastic_states': 3,
                           'early_coin_no_revelation_deterministic_states': 4},
              'scope': 'Finite construction and support-certificate checks; optimality and arbitrary-state exclusion are proved separately.'}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
