#!/usr/bin/env python3
"""Independent reproducible checks, not a proof of the global width theorem.

Requires Python >=3.10, standard library only. Exact checks use Fraction.
Classifier checks sum independent binomial distributions deterministically;
they do not simulate trajectories or enumerate exponentially many words.
"""
from bisect import bisect_right
from fractions import Fraction as F
from itertools import product
import hashlib
import json
import math
from pathlib import Path
import random
import sys


def mm(a, b):
    return [[sum((x * y for x, y in zip(r, c)), F(0))
             for c in zip(*b)] for r in a]


def tr(a):
    return list(map(list, zip(*a)))


def diag(xs):
    return [[x if i == j else F(0) for j in range(len(xs))]
            for i, x in enumerate(xs)]


def eye(n):
    return diag([F(1)] * n)


def add(a, b):
    return [[x + y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(a, c):
    return [[c * x for x in r] for r in a]


def total(matrices):
    out = scale(matrices[0], F(0))
    for a in matrices:
        out = add(out, a)
    return out


def val(rho, kernels, word):
    for y in word:
        rho = mm(rho, kernels[y])
    return sum(rho[0])


def rank(a):
    a = [r[:] for r in a]
    out = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(out, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[out], a[pivot] = a[pivot], a[out]
        a[out] = [x / a[out][j] for x in a[out]]
        for i in range(len(a)):
            if i != out:
                coeff = a[i][j]
                a[i] = [x - coeff * y for x, y in zip(a[i], a[out])]
        out += 1
        if out == len(a):
            break
    return out


def words(d, length):
    for n in range(length + 1):
        yield from product(range(d), repeat=n)


def stochastic(a):
    assert all(sum(r) == 1 and min(r) >= 0 for r in a)


def exact_checks():
    p, m, d, k = 3, 3, 4, 7
    pi = [[F(int(j == (i + 1) % p)) for j in range(p)] for i in range(p)]
    pi_inv = tr(pi)
    v = [[F(7 if a == y else 3, 16) for y in range(d)] for a in range(p)]
    q = [[F(1, 3), F(2, 3), F(0), F(0), F(0), F(0), F(0)],
         [F(0), F(0), F(1, 4), F(3, 4), F(0), F(0), F(0)],
         [F(0), F(0), F(0), F(0), F(2, 5), F(3, 5), F(0)]]
    l = [eye(p)[a] for a in (0, 0, 1, 1, 2, 2)] + [[F(1, 2), F(1, 3), F(1, 6)]]
    assert mm(q, l) == eye(p)
    stochastic(q)
    stochastic(l)
    phase = [mm(diag([r[y] for r in v]), pi) for y in range(d)]
    native = [mm(mm(l, a), q) for a in phase]
    transition = mm(mm(l, pi), q)
    assert total(native) == transition
    stochastic(transition)
    emission = [mm(l, [[r[y]] for r in v]) for y in range(d)]
    before = [mm(diag([r[0] for r in e]), transition) for e in emission]
    after = []
    for y in range(d):
        shifted = mm(mm(pi_inv, diag([r[y] for r in v])), pi)
        shifted_e = mm(mm(l, shifted), [[F(1)]] * p)
        after.append(mm(transition, diag([r[0] for r in shifted_e])))
    assert after == native
    # The emission-first kernels need only intertwine on the reachable split.
    assert before != native
    assert all(mm(q, a) == mm(b, q) for a, b in zip(before, phase))
    weights = [[F(1), F(0), F(0)], [F(2, 3), F(1, 3), F(0)], [F(1, 3)] * 3]
    tested = 0
    for w in weights:
        rho = mm([w], q)
        for word in words(d, 4):
            target = sum(w[a] * math.prod(v[(a + t) % m][y] for t, y in enumerate(word))
                         for a in range(p))
            assert val([w], phase, word) == target
            assert val(rho, native, word) == target
            assert val(rho, before, word) == target
            assert val(rho, after, word) == target
            tested += 1
    rho = mm([weights[0]], q)
    wrong = [mm(transition, diag([r[0] for r in e])) for e in emission]
    wrong_first = val(rho, wrong, (0,))
    right_first = val(rho, native, (0,))
    assert wrong_first == F(3, 16) != right_first == F(7, 16)

    # A genuinely transient native initial state plus an unreachable state.
    # States 0..2 are canonical phases, state 3 is used only at time zero,
    # and state 4 is unreachable and has unrelated IID uniform emissions.
    transient = []
    w = weights[1]
    for y in range(d):
        a = [[F(0)] * 5 for _ in range(5)]
        for i in range(p):
            a[i][:p] = phase[y][i]
        a[3][:p] = mm([w], phase[y])[0]
        a[4][4] = F(1, d)
        transient.append(a)
    tt = total(transient)
    stochastic(tt)
    rr = [[F(0), F(0), F(0), F(1), F(0)]]
    bar = scale(rr, F(0))
    cur = rr
    for _ in range(m):
        bar = add(bar, scale(cur, F(1, m)))
        cur = mm(cur, tt)
    assert bar != mm(bar, tt)
    assert bar[0][3] == F(1, 3)
    averaging_words = 0
    for word in words(d, 3):
        target = val([w], phase, word)
        assert val(rr, transient, word) == target
        shifted = sum(val(rr, transient, u + word)
                      for r in range(m) for u in product(range(d), repeat=r)) / m
        averaged = val(bar, transient, word)
        assert averaged == shifted == val([[F(1, p)] * p], phase, word)
        assert averaged == sum(val(bar, transient, (y,) + word) for y in range(d))
        averaging_words += 1

    # Exact finite rank witness, including initially zero weights.
    prefixes = [(), (0,), (0, 0)]
    suffixes = [(), (0,), (1,)]
    hankel = [[val([weights[0]], phase, u + z) for z in suffixes] for u in prefixes]
    assert rank(hankel) == 3
    aligned = [(), (0, 0, 0), (1, 2, 3)]
    assert rank([[val([weights[0]], phase, u + z) for z in aligned] for u in aligned]) == 1
    stationary = [[F(1, p)] * p]
    pair = [[val(stationary, phase, (y, z)) for z in range(d)] for y in range(d)]
    assert pair == scale(mm(mm(tr(v), pi), v), F(1, p))
    assert pair[0][1] != pair[1][0]
    assert rank(v) == p

    # Reproducible symmetry tests use exact probabilities, not simulation.
    rng = random.Random(20261104)
    for _ in range(100):
        word = [rng.randrange(d) for _ in range(12)]
        rearranged = word[:]
        for r in range(m):
            row = word[r::m]
            rng.shuffle(row)
            rearranged[r::m] = row
        assert val([weights[1]], phase, word) == val([weights[1]], phase, rearranged)

    # Negative controls expose the necessity of specific hypotheses.
    a, b = F(1, 5), F(4, 5)
    def alternating(word):
        return math.prod((a if t % 2 == 0 else b) if y else
                         (1 - (a if t % 2 == 0 else b)) for t, y in enumerate(word))
    one = [(), (1,)]
    blocks = [(), (1, 1), (0, 1)]
    assert rank([[alternating(u + z) for z in one] for u in one]) == 2
    assert rank([[alternating(u + z) for z in blocks] for u in blocks]) == 1
    assert sum(alternating((y, 1)) for y in range(2)) == b != alternating((1,)) == a
    def correlated(word):
        out = F(1)
        for t in range(0, len(word), 2):
            if t + 1 < len(word) and word[t] != word[t + 1]:
                return F(0)
            out *= F(1, 2)
        return out
    assert correlated((0, 0, 1, 1)) == F(1, 4)
    assert correlated((0, 1, 1, 0)) == 0
    assert correlated((0, 0)) == F(1, 2)
    assert sum(correlated((y, 0, 0)) for y in range(2)) == F(1, 4)
    invisible = [scale(pi, F(2, 5)), scale(pi, F(3, 5))]
    small_words = list(words(2, 2))
    assert rank([[val([[F(1), F(0), F(0)]], invisible, u + z)
                  for z in small_words] for u in small_words]) == 1
    # For deterministic three-phase outputs and one-symbol classifiers,
    # adjacent blocks have joint table Pi/3, not I/3. Length must align.
    assert scale(pi, F(1, 3)) != scale(eye(3), F(1, 3))
    return {
        "exact_word_lift_comparisons": tested,
        "parameter_weights": [[str(x) for x in w] for w in weights],
        "ordinary_hmm_conventions": "Both agree on all tested words; transition-first uses predecessor-phase emissions.",
        "emission_first_kernels_equal_lift": False,
        "transition_first_kernels_equal_lift": True,
        "wrong_unshifted_transition_first_p0": str(wrong_first),
        "correct_p0": str(right_first),
        "native_transient_averaging_word_checks": averaging_words,
        "native_averaged_hidden_distribution": [str(x) for x in bar[0]],
        "native_averaged_hidden_distribution_is_stationary": False,
        "native_averaged_output_law_is_stationary_on_checked_words": True,
        "ordinary_hankel_rank_witness": rank(hankel),
        "initial_aligned_block_hankel_rank": 1,
        "stationary_order_witness_p01_p10": [str(pair[0][1]), str(pair[1][0])],
        "residue_permutation_checks": 100,
        "negative_controls_passed": [
            "Unshifted transition-first emissions give the wrong first output.",
            "Initial aligned-block rank can undercount ordinary phase rank.",
            "Whole-block exchangeability need not imply residue-wise symmetry or stationarity.",
            "A supplied hidden three-cycle with identical emissions has observable rank one.",
            "Unaligned adjacent classifier blocks have a phase-shifted joint table.",
        ],
    }


def binomial(n, probability):
    probability = float(probability)
    out = [math.exp(math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)
                    + k * math.log(probability) + (n - k) * math.log1p(-probability))
           for k in range(n + 1)]
    norm = math.fsum(out)
    return [x / norm for x in out], abs(norm - 1)


def h(z, delta):
    if z <= delta / 8:
        return F(1)
    if z < delta / 4:
        return 2 - 8 * z / delta
    return F(0)


def bump_expectation(pmf, reference, t, delta):
    """E h(max_r |K_r/t-reference_r|) by the exact finite support of max.

    Counts are independent. The max CDF is a product of three row CDFs.
    Grid and h breakpoints are rational; only binomial masses are float.
    """
    row_cdfs = []
    grid = set()
    for masses, center in zip(pmf, reference):
        grouped = {}
        for k, mass in enumerate(masses):
            distance = abs(F(k, t) - center)
            grouped.setdefault(distance, []).append(mass)
        distances = sorted(grouped)
        accum = []
        running = 0.0
        for distance in distances:
            running += math.fsum(grouped[distance])
            accum.append(running)
        row_cdfs.append((distances, accum))
        grid.update(distances)
    terms = []
    previous = 0.0
    for distance in sorted(grid):
        if distance >= delta / 4:
            break  # h is zero from here onward.
        cdf = 1.0
        for distances, accum in row_cdfs:
            index = bisect_right(distances, distance) - 1
            cdf *= accum[index] if index >= 0 else 0.0
        increment = cdf - previous
        assert increment >= -1e-14
        terms.append(float(h(distance, delta)) * max(0.0, increment))
        previous = cdf
    return math.fsum(terms)


def fm(a, b):
    return [[math.fsum(x * y for x, y in zip(r, c)) for c in zip(*b)] for r in a]


def close(a, b, tolerance=2e-12):
    assert len(a) == len(b) and all(len(r) == len(s) for r, s in zip(a, b))
    error = max(abs(x - y) for r, s in zip(a, b) for x, y in zip(r, s))
    assert error <= tolerance, error
    return error


def repair(q, l):
    p, k = len(q), len(l)
    unnormalized = [[q[a][i] * max(0.0, l[i][a] - 0.75) for i in range(k)] for a in range(p)]
    denominators = [math.fsum(r) for r in unnormalized]
    assert min(denominators) > 0
    qp = [[x / denom for x in r] for r, denom in zip(unnormalized, denominators)]
    lp = []
    for i in range(k):
        dd = [min(1.0, max(0.0, 12 * (l[i][a] - 2 / 3))) for a in range(p)]
        assert sum(x > 0 for x in dd) <= 1
        lp.append([x + (1 - math.fsum(dd)) / p for x in dd])
    error = close(fm(qp, lp), [[float(a == b) for b in range(p)] for a in range(p)])
    close([[math.fsum(r)] for r in qp], [[1.0]] * p)
    close([[math.fsum(r)] for r in lp], [[1.0]] * k)
    assert min(min(r) for r in qp + lp) >= -2e-12
    return min(denominators), error


def classifier_checks():
    p, m, d = 3, 3, 2
    initial = [F(1, 10), F(1, 2), F(9, 10)]
    profiles = [initial[a:] + initial[:a] for a in range(p)]
    delta = min(max(abs(x - y) for x, y in zip(a, b))
                for i, a in enumerate(profiles) for j, b in enumerate(profiles) if i != j)
    wmin = 1 / p
    t = math.ceil(32 / float(delta) ** 2 * math.log(16 * m * d / wmin))
    n = m * t
    epsilon = 2 * m * d * math.exp(-t * float(delta) ** 2 / 32)
    assert epsilon <= wmin / 8
    distributions = [binomial(t, x) for x in initial]
    norm_error = max(x[1] for x in distributions)
    pmfs = [x[0] for x in distributions]
    c = []
    for a in range(p):
        actual = pmfs[a:] + pmfs[:a]
        bump = [bump_expectation(actual, reference, t, delta) for reference in profiles]
        leftover = 1 - math.fsum(bump)
        assert leftover >= -2e-12
        c.append([value + leftover / p for value in bump])
    close([[math.fsum(r)] for r in c], [[1.0]] * p)
    assert all(c[a][a] >= 1 - epsilon for a in range(p))
    marg = [math.fsum(c[a][i] / p for a in range(p)) for i in range(p)]
    joint = [[math.fsum(c[a][i] * c[a][j] / p for a in range(p)) for j in range(p)] for i in range(p)]
    ratio = [joint[i][i] / marg[i] for i in range(p)]
    assert min(ratio) >= 6 / 7
    q = [[c[a][i] / (p * marg[i]) for a in range(p)] for i in range(p)]
    split = fm(q, c)
    close(split, [[joint[i][j] / marg[i] for j in range(p)] for i in range(p)])
    denominator, error = repair(q, c)
    assert denominator >= 3 / 28

    # Actual competitor: mix the stationary target with a permanently zero
    # output state of mass beta. This is a width-four native realization.
    # Its TV error is <=beta at every horizon, by the mixture coupling.
    beta = wmin / 64
    # Construct this competitor explicitly, and verify the mixture law and
    # its TV distance at a short horizon using rational arithmetic.
    beta_exact = F(1, 192)
    phase_kernels = []
    contaminated_kernels = []
    for y in range(d):
        phase_kernel = [[F(0)] * p for _ in range(p)]
        candidate_kernel = [[F(0)] * (p + 1) for _ in range(p + 1)]
        for a in range(p):
            emission = initial[a] if y else 1 - initial[a]
            phase_kernel[a][(a + 1) % p] = emission
            candidate_kernel[a][(a + 1) % p] = emission
        candidate_kernel[p][p] = F(int(y == 0))
        phase_kernels.append(phase_kernel)
        contaminated_kernels.append(candidate_kernel)
    stochastic(total(contaminated_kernels))
    target_rho = [[F(1, p)] * p]
    candidate_rho = [[(1 - beta_exact) / p] * p + [beta_exact]]
    total_variation = F(0)
    for word in product(range(d), repeat=8):
        target_probability = val(target_rho, phase_kernels, word)
        candidate_probability = val(candidate_rho, contaminated_kernels, word)
        assert candidate_probability == ((1 - beta_exact) * target_probability
                                         + beta_exact * int(not any(word)))
        total_variation += abs(candidate_probability - target_probability) / 2
    assert total_variation == beta_exact * (1 - val(target_rho, phase_kernels, (0,) * 8))
    assert total_variation <= beta_exact
    zero_bumps = [float(h(max(reference), delta)) for reference in profiles]
    noise = [b + (1 - math.fsum(zero_bumps)) / p for b in zero_bumps]
    lcandidate = c + [noise]
    rr = [[(1 - beta) * c[a][i] / p for a in range(p)] + [beta * noise[i]] for i in range(p)]
    mcandidate = [math.fsum(row) for row in rr]
    qcandidate = [[x / mcandidate[i] for x in row] for i, row in enumerate(rr)]
    jcandidate = fm(rr, lcandidate)
    close(jcandidate, [[(1 - beta) * joint[i][j] + beta * noise[i] * noise[j]
                        for j in range(p)] for i in range(p)])
    assert max(abs(x - y) for x, y in zip(marg, mcandidate)) <= beta + 2e-12
    assert max(abs(joint[i][i] - jcandidate[i][i]) for i in range(p)) <= beta + 2e-12
    margin = [jcandidate[i][i] - 0.75 * mcandidate[i] for i in range(p)]
    assert min(margin) > 0
    assert min(joint[i][i] - 0.75 * marg[i] for i in range(p)) >= 3 * wmin / 32
    perturbed_ratio = [jcandidate[i][i] / mcandidate[i] for i in range(p)]
    assert min(perturbed_ratio) > 0.75
    pdenominator, perror = repair(qcandidate, lcandidate)

    # Negative control: an uninformative classifier table has no split.
    bad = [[1 / p] * p for _ in range(p)]
    bad_diag = [fm(bad, bad)[i][i] for i in range(p)]
    assert max(bad_diag) < 0.75
    assert all(math.fsum(bad[a][i] * max(0.0, bad[i][a] - 0.75)
                         for i in range(p)) == 0 for a in range(p))
    return {
        "method": "Deterministic independent-binomial sums; no Monte Carlo.",
        "binary_phase_success_probabilities": [[str(x) for x in r] for r in profiles],
        "delta": str(delta), "averaged_minimum_weight": wmin,
        "cycles_t": t, "block_length_n": n,
        "nonstationary_robust_horizon_2n_plus_m_minus_1": 2 * n + m - 1,
        "stationary_robust_horizon_2n": 2 * n,
        "hoeffding_epsilon_bound": epsilon,
        "largest_binomial_normalization_error_before_normalization": norm_error,
        "classifier_table_C": c,
        "smallest_C_diagonal": min(c[a][a] for a in range(p)),
        "smallest_conditional_joint_diagonal": min(ratio),
        "repair_minimum_denominator": denominator,
        "repair_identity_max_abs_error": error,
        "contamination_beta_and_all_horizon_TV_upper_bound": beta,
        "contaminated_native_width": 4,
        "contaminated_exact_length_8_word_checks": 2 ** 8,
        "contaminated_length_8_TV_exact": str(total_variation),
        "smallest_contaminated_conditional_joint_diagonal": min(perturbed_ratio),
        "smallest_contaminated_3_over_4_margin": min(margin),
        "contaminated_repair_minimum_denominator": pdenominator,
        "contaminated_repair_identity_max_abs_error": perror,
        "uninformative_classifier_negative_control": "Diagonal 1/3; every repair denominator is zero, as expected.",
    }


def main():
    manuscript = Path(__file__).resolve().parents[1] / "periodic_phase_observable_theorem.tex"
    result = {
        "all_checks_passed": True,
        "python_version": sys.version.split()[0],
        "dependencies": "Python >=3.10 standard library only",
        "manuscript_sha256_at_run": hashlib.sha256(manuscript.read_bytes()).hexdigest(),
        "exact_rational_checks": exact_checks(),
        "floating_point_classifier_and_robustness_checks": classifier_checks(),
        "scope": "Finite algebraic identities, witnesses, and deterministic floating-point classifier tests only. These do not establish the Moore-space obstruction, section existence, continuity over a parameter space, general reconstruction, or any theorem about infinite word laws.",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
