# Independent mathematical and reproducibility review

Date: 2026-11-02. Status: **PASS within the explicitly stated finite, exact, time-homogeneous scope.**

This is a separate-agent proof review and execution check, not proof-assistant verification, exhaustive literature clearance, or certification of physical realizability. The TeX has not been compiled or visually inspected. No novelty conclusion is certified.

## Exact reviewed artifacts

| Artifact | SHA-256 |
|---|---|
| `Native_Realization_Refinement_Reduction_Test.tex` | `ca2452782f6ce22d9cc9f320567e93df8e0e908d4422729136f191ccb578f7de` |
| `checks/verify_partition_refinements.py` | `a8f78284d11215081b18683c8eb3534f2c2ba6317613988eb13320c79ada3296` |
| `checks/expected_results.json` | `c4df1bd5fc036fb48850394d36be0c30c8ae52642baf1437b6c66ff194d44fac` |
| `checks/reproduce.py` | `33d774f9c16cadbdb432bc83748d0758404fb4cef095d6d1b0037757ce08ec5e` |

The finding applies to these versions; later modifications require rechecking.

## Proof review

1. **Comparison discipline.** The labelled stochastic intertwining equations preserve joint output/next-state kernels. Their strength beyond initial trace equality, their direction, and the difference between stochastic and deterministic state comparisons are explicit. The obstruction is not represented as impossibility of realizing the richer behavior from scratch.

2. **Complete bounded behavior-only reduction.** The invariant row-space certificate contains the initial difference row, is invariant under every action/output matrix, and annihilates the terminal ones vector. Its necessity and sufficiency enforce every finite fine word probability. The candidate need not map to the supplied fine generator. Degree-two real constraints, padding to the budget, and the real-versus-rational coefficient and unbounded-decision limitations are correct.

3. **Fixed-presentation coupling reduction.** Necessity follows by pushing each representative state's kernel through the two deterministic maps. Sufficiency selects supported couplings on the stable relation. The product bound belongs to this stronger problem only. The early/late example correctly shows that its failure need not defeat behavior-only synthesis.

4. **Two-stage feasibility.** Every candidate induces the nonnegative joint matrix T with TQ=R and the prescribed column masses. Conversely that matrix gives an identity-projection realization on the chosen coarse states. This is an independent linear feasibility criterion, not an assumption that a realization already exists.

5. **Exact stochastic resource cost.** The upper construction normalizes a nonnegative factorization. For the lower bound, disjoint next-output alphabets force disjoint supports at times zero, one, and two in every homogeneous candidate. The intermediate comparison rows factor T, proving the lower bound even with arbitrary initial mixtures, extra terminal states, and unreachable states. Charging root/terminal phase memory is essential and explicit. The deterministic bound follows from reachability of every coarse state.

6. **Blackwell orientation.** Bayes-transposed experiments satisfy E=DL exactly when the transport matrix is feasible. Zero-probability outcome columns are legitimately removed. The assertion concerns existence of a compatible conditional-independence coupling, not an arbitrary pre-existing joint law.

7. **Partition specialization.** Coarse partition B must refine announcement partition D, not conversely. Positive weights force the unique feasible matrix; disjoint nonzero row supports give its exact nonnegative rank. The formulas |D|+2 and |B|+2 follow, as does impossibility at every finite budget when containment fails.

8. **Full-support controls.** The symmetric 0.8-accuracy coarse channel has inverse with diagonal 4/3 and off-diagonal -1/3. The three proposed joint laws force, respectively, a nonnegative rank-one matrix, a nonnegative rank-two matrix, and a matrix with off-diagonal -1/12. This verifies costs three and four and an infeasible case without relying on support zeros.

No unresolved mathematical defect was found in these arguments. Source attribution is presented as a bounded audit and adaptations are separated from cited theorems; this review independently checked the mathematics, not every source passage.

## Reproducibility

Independently ran `python checks/reproduce.py`, which executes temporary clean copies of the checker both normally and with `python -O`. Both runs returned no stderr and byte-identical expected JSON under Python 3.12.14.

- 5,917 declared partition/probability instances.
- 867 feasible cases, each with stochastic and deterministic witnesses.
- 5,050 support-obstruction certificates.
- 718 strict state-cost gaps.
- 867 positive transport/rank certificates.
- Three additional full-support binary noisy-channel controls: two feasible sharp costs and one exact infeasibility certificate.

The code was inspected for the relevant construction, stochasticity, initial comparison, labelled kernel equations, target word laws, support certificates, and phase counts. Its explicit `require` checks remain active under optimization. These computations verify a finite roster and concrete certificates; they do not enumerate all latent realizations or replace the general proofs of optimality and unbounded obstruction.

## Acceptance boundary

This package supports a focused reduction-test conclusion: established simulation, real-algebra, coupling, garbling, and nonnegative-factorization techniques solve the stated bounded problem and the stated two-stage class. It does not establish a new general phenomenology theory, a general unbounded realization algorithm, rational-only synthesis, an efficient minimum-rank algorithm, learned observation acquisition, or a physical implementation theorem.
