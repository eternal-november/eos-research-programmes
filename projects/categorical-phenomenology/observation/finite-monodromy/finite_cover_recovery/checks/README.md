# Reproducible checks for finite cover recovery

These checks accompany `../finite_cover_recovery.tex`. They test finite algebra, probability constants, the actual clustering/matching algorithm, and its stated failure boundaries. They do not prove the theorem or certify its model promises from observations.

The final checked source SHA256 is `137724f0f1c29d3a84180513282ead25567df6281a564ff6b4424c37f59132d2`. The last source update only changed the periodic-section heading to “randomized offsets reveal initially absent phases”; all checks were rerun, with unchanged numerical results.

## Run

Requirements: Python 3.10 or newer and NumPy 1.24 or newer. The stored run used Python 3.12.14 and NumPy 2.3.5.

```sh
python finite_cover_recovery/checks/verify.py \
  > finite_cover_recovery/checks/results.json
```

The fixed seed is `202611040032`. The report records the source SHA256. Every asserted deterministic identity and every implication from the theorem's good event must pass; failures raise an exception. Monte Carlo success rates are reported, not used as proof of the stated confidence guarantee. Random streams can differ between NumPy versions.

Long IID trajectories are sampled through multinomial sufficient statistics. This is exactly the distribution of their empirical frequency vectors, not a Gaussian approximation or a shorter observation model. Reported symbol budgets refer to the equivalent original experiments, not the amount of memory materialized by the script.

## Nontrivial held-IID covers

For p=2 and p=3, the four-symbol emission atoms form a regular polygon in a two-dimensional interior patch of the probability simplex. As the parameter goes once around the known circle, the polygon turns through one vertex spacing. This gives a transposition or a three-cycle, respectively.

The fixtures use amplitude 1/8, uniform weights, conservative separation `sqrt(2)*amplitude*sin(pi/p)`, and lifted speed `amplitude/p`. They satisfy the endpoint gluing and mesh hypotheses. The script uses the manuscript's exact ceiling formulas, with alpha=0.05:

| Cover | Mesh vertices | Restarts per vertex | Symbols per restart | Sufficient union failure bound |
|---|---:|---:|---:|---:|
| Two-sheet transposition | 18 | 15 | 11,640 | 0.04489993 |
| Three-sheet three-cycle | 14 | 23 | 15,760 | 0.04466098 |

In the recorded 300 trials per fixture, both fixtures recovered the correct cycle type in 299 trials. Each fixture had one missing-component coverage event and no empirical-frequency event outside the promised error radius. Every theorem-good event recovered exact clusters, correct edge transports, and the true monodromy in the estimated starting labels.

The code sees empirical vectors only when clustering and matching. Hidden labels are used afterward to check the mathematical guarantees, never to choose a recovered edge or a cluster.

## Labels and conjugacy

Independent vertex label changes transform each recovered edge by the appropriate two-sided permutation change. The product around the circle changes by conjugation at the starting vertex. The stored three-cycle changes from `[2,0,1]` to `[1,2,0]` under relabeling, while its cycle type remains `[3]`.

This also checks that full monodromy contains more information than its sign: the three-cycle and identity both have positive sign, but different cycle types and different stochastic-width decisions under the imported classification theorem.

## Unknown component count and bounded corruption

- With the supplied lower weight bound 1/4, the unknown-p procedure uses the upper bound P=4, then recovers the actual count three from the common number of empirical clusters.
- A separate run adds label- and vertex-dependent coordinate corruption of size eta=delta/16 to every empirical vector, preserving the simplex. The adjusted length is 63,040, four times the clean length. It recovers the same three-cycle on the stated good event.
- The input boundary eta=delta/8 is rejected, since the stated concentration margin then vanishes.

## Periodic randomized offsets with zero initial mass

The periodic fixture has period three and the same nontrivial three-sheet cover. Its profile for sheet a is the ordered emission triple `(v_a,v_(a+1),v_(a+2))`. It uses continuous initial weights

```text
w_a(theta) = [1 + cos(theta/3 + 2*pi*a/3)] / 3.
```

These weights obey the cover's cyclic gluing. At the midpoint vertex one phase has initial weight exactly zero, so a positive global initial-mass bound is unavailable. The rotation-averaged weights are all 1/3.

Each restart draws a fresh independent offset. The simulation draws and discards the original prefix, then samples the retained residue counts under the correctly shifted profile. With t=17,260, it recovers all phases, the three-cycle monodromy, and the phase-advance permutation. It verifies the finite identities

```text
tau_i^3 = identity
T_i tau_i = tau_(i+1) T_i
sigma tau_0 = tau_0 sigma.
```

The equivalent original experiment observes 16,673,485 symbols in the stored run, within the worst-case bound 16,673,804 including discarded prefixes.

Two controls distinguish different offset assumptions:

1. Without offsets, the zero-mass phase cannot occur at the midpoint vertex.
2. Even marginally uniform offsets do not suffice without independence: if S is uniform and U=-S modulo three, the offset is uniform but every retained experiment starts in phase zero.

## Boundary and negative controls

- At equality `Lh+2r=delta/2`, a true match can lie exactly at the strict edge threshold and the relation need not be a bijection.
- With estimation radius delta/4 rather than delta/8, two empirical vectors from one atom can split into two clusters at the threshold.
- A half-twist hidden entirely inside an unobserved arc has the same sampled unordered fibers as a trivial cover. The algorithm returns identity although the hidden cover has transposition monodromy. This deliberately violates the required mesh/modulus bound.
- A three-point measure can be arbitrarily close in transportation distance to a two-point measure by splitting one atom into two nearby atoms. The at-most-p support promise is essential.
- At equality `W1=w0*r`, an estimated atom can lie exactly at distance r, so the open-ball conclusion requires the strict hypothesis.

These are controls outside the stated assumptions, not counterexamples to the theorem.

## Lower-bound constants and limitations

On a 1,001-point angular grid in the rare-sheet construction, the code checks the rare categorical KL bound and its mixture-weighted version. The largest checked augmented one-symbol KL is approximately 0.05493061, about 0.27465307 of the claimed uniform bound for the chosen parameters. It also reports sample values of the restart and symbol error lower bounds.

These checks do not establish the adaptive-design chain rule, optimality, novel priority, global model promises, or the imported arbitrary-native width classification. No mathematical counterexample satisfying every stated hypothesis was found in the accompanying review.
