# Reproducible finite checks for the periodic-phase manuscript

These checks **complement the proofs; they do not prove the topological width theorem**. In particular, no finite calculation below establishes the Moore-space obstruction, a global continuous section, or identifiability from finite data.

## Reproduce

Requirements: Python 3.10 or newer, standard library only. No installation, network connection, NumPy, symbolic-algebra package, or Monte Carlo is needed.

From the package root:

```sh
python3 periodic_checks/verify.py \
  > periodic_checks/results.json
```

The script exits nonzero if any assertion fails. The stored run passed with Python 3.12.14. Its JSON records the manuscript SHA256. Float values may vary in their final digits across Python/platform math libraries. The algebraic checks use exact rational arithmetic and are independent of floating-point tolerances.

The neighboring `../check_periodic_phase.py` is the author's separate rational checker. This directory is an independent, complementary implementation, particularly for native transience and deterministic classifier/robustness calculations.

## Exact rational fixture

The main fixture has three phases, period three, four symbols, and emission rows

```text
(7,3,3,3)/16
(3,7,3,3)/16
(3,3,7,3)/16.
```

Its seven-slot stochastic split includes two copies of each phase and one unused native slot with a mixed decoder. The initial weights are `(1,0,0)`, `(2/3,1/3,0)`, and `(1/3,1/3,1/3)`.

All 341 words of length at most four are checked for each weight vector, giving 1,023 exact word/weight cases. Each case compares the direct profile law, canonical phase realization, split lift, emission-then-transition HMM, and transition-then-emission HMM.

Results and useful distinctions:

- Both ordinary HMM conventions produce the same word law.
- The correct transition-first kernels equal the lift. The emission-first kernels need not equal the lift on an unused native slot, but satisfy the required intertwining identity and produce the same outputs.
- Omitting the predecessor-phase shift from transition-first emissions gives first-symbol probability `3/16`, instead of the correct `7/16`.
- An exact finite ordinary Hankel minor has rank three even when initial phase weights vanish. A tested aligned-block Hankel matrix has rank one for the single-initial-phase fixture.
- The stationary four-symbol fixture is nonexchangeable already at length two: `p(01)=67/768`, whereas `p(10)=17/256`.
- One hundred seeded independent residue-row permutation tests preserve the exact word probabilities. These are reproducible test cases, not a finite certificate of infinite residue symmetry.

## Averaging an arbitrary native presentation

A second realization has the three canonical phases, one transient state used only initially, and one unreachable state with unrelated uniform emissions. For 85 words of length at most three, the script exactly verifies the original law, the observable prefix-sum averaging formula, agreement with the uniform phase average, and output stationarity.

The averaged native initial distribution is

```text
(1/9, 2/9, 1/3, 1/3, 0).
```

It is **not** stationary for the native hidden transition matrix, even though its output law agrees with the stationary phase-average law on every tested word. This directly exercises the proof's distinction between stationary output laws and stationary hidden presentations.

## Deterministic classifier and robustness checks

For an independent binary fixture, the success-probability profiles are the three rotations of `(1/10,1/2,9/10)`. Their separation is `delta=4/5`, and averaged weights are `1/3`. The manuscript's formula gives:

- `t=284` cycles;
- classifier block length `n=852`;
- Hoeffding error upper bound approximately `0.04096270`;
- robust horizons `2n=1704` for stationary targets and `2n+m-1=1706` after shift averaging.

The classifier table is evaluated deterministically by summing binomial distributions. For each candidate profile, the empirical-profile maximum-distance CDF is the product of three row CDFs. The script sums the exact rational-grid hat-function values against these floating-point CDF increments. It does not enumerate `2^852` words and does not sample trajectories.

The observed diagonal of the classifier table is approximately `0.99996293`; the smallest conditional two-block diagonal is `0.99992586`, above `6/7`. The exact-split threshold formulas return the identity with maximum floating-point residual `0.0` in the stored run.

The robustness competitor mixes the stationary target with a permanently zero-output state of mass `beta=1/192`, giving a concrete width-four realization. The mixture coupling bounds its total variation error by `beta` at **every** horizon. Its kernels and all 256 length-eight word probabilities are also verified with rational arithmetic; the exact short-horizon total variation distance is recorded in the JSON.

For this competitor, the smallest conditional two-block diagonal is approximately `0.99645403`, and the smallest gap `J_ii-(3/4)a_i` is approximately `0.08215134`. The same-width repair again returns the identity with maximum floating-point residual `0.0` in this run. This tests the finite-table algebra of the robustness proof. It does not prove a uniform family-level lower bound.

## Negative controls

The script verifies the expected failure of five tempting shortcuts:

1. Unshifted transition-first emissions give the wrong law.
2. Initial aligned-block rank may be smaller than the full ordinary rank.
3. IID correlated pairs are whole-block exchangeable but fail residue-wise symmetry and one-symbol stationarity: `p(0011)=1/4` and `p(0110)=0`.
4. A hidden three-cycle with identical phase emissions has observable rank one.
5. For deterministic cyclic outputs, unaligned one-symbol classifier blocks have joint table `Pi/3`, rather than the falsely assumed `I/3`.

An additional numerical negative control uses completely uninformative classifiers. Its conditional diagonal is `1/3`, and every threshold-repair denominator is zero, as it should be. The code therefore does not merely report successful repairs without checking the separation hypothesis.
