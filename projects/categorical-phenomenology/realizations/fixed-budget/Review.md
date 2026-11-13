# Mathematical and reproduction review

Review date: 3 November 2026.

## Exact reviewed artifact

- File: `report.tex`
- SHA-256: `b9c41fca943a9d0a761bc42552f5c1a38e5892363ade091d0a81b700aa52e677`
- README SHA-256: `fc87a3dd79bd3d8eda4096c003d94acf1c84067af89360b1e5576698518d4f93`

**Result:** no unresolved mathematical defect was found in the stated results and proofs. The conclusions are valid for the declared finite layer-native class and the displayed residual system. This review is not a novelty clearance, a formal proof-assistant verification, or a certification of a general optimization solver. Any change to the report requires a new hash comparison and review of the changed claims.

## Proof obligations checked

1. **At-most-budget equivalence.** Binary selectors and the cap slack force each slot to have zero or one tuple label. The root and row gates force all inactive root and continuation entries to zero. Active slots give stochastic rows in the prescribed coupling polytope. The target mass equations ensure that at least one active state has incoming mass. Conversely, every implementation with at most K middle states has a real square-slack lift. The bound on each root entry follows from total root mass one. Root and terminal add two states.
2. **Degenerate cases.** Empty coupling polytopes cannot label active slots but do not obstruct unused slots. Zero announcement and retained masses require no divisions. The rank-zero convention for a zero block, including an empty row polytope, is preserved. At K=0 the objective is the stated strictly positive constant on the zero-dimensional domain.
3. **Polynomial size and degree.** The coordinate count is K(|E|+1+3|J|+2|S|). Every residual has degree at most two, the objective at most four, and the gradient at most three. Existential-real membership is restricted to rational coefficients and explicit input tables; capping a binary budget by |J||E| is justified by the unrestricted reconstruction bound.
4. **Attainment.** Every coordinate is explicitly bounded on every sublevel: selectors, activity slack, root variables and both root slacks, continuation entries, and continuation slacks. Closed sublevels are compact. Consequently infeasibility implies an attained strictly positive global minimum, rather than merely the absence of a zero. Positive weighting preserves coercivity through the minimum weight. The optional circle completion and its Cauchy–Schwarz lower bound are valid and are not needed for the original proof.
5. **Optimizer counterexamples.** The all-inactive point has exactly the stated positive objective and zero gradient. The weighted singleton example has a feasible zero and a strict positive local minimum. Its lower-bound coefficients 14, 94, 97, and 96, equality conditions, Hessian block, and principal minors were checked. The strict-local-minimum claim is correctly restricted to the weighted example. The small-residual incompatible family has residual exactly 2 epsilon squared and varies the input, so it does not contradict fixed-instance attainment.
6. **Dynamical scope.** The energy identity and compact-sublevel continuation argument prove forward global existence of the exact gradient flow. They do not prove zero limiting loss. The scalar quartic Euler example correctly excludes a universally stable fixed positive step on the whole space.
7. **Compositional scope.** The shared-variable gradient identity is an ordinary chain-rule identity. Full local Euler maps cannot be gathered with the continuous-field rule because it duplicates identity contributions. Increment transport supplies the stated naturality identity. Native-witness transport, canonical optimizer selection, arbitrary-coordinate trajectory invariance, and a contextad identification are explicitly left unproved.
8. **Exact certificates.** The equality-only real Nullstellensatz identity has the correct sign and sum-of-squares form. Transfer to real algebraic witnesses and certificate coefficients is justified for rational input by real-closed-field quantifier elimination. No rational-factor, bounded certificate degree, or small certificate-size claim is made.

## Sources independently cross-checked

- Hanks, Fairbanks, and Klawonn, [2025 final version](https://arxiv.org/html/2403.19845v2), Theorem 3.5 and Corollary 3.5.1: the negative-gradient assignment and gradient-flow hypergraph functor, with the separate finite-limit assumption and separate Euler discussion.
- Parrilo, [Semidefinite Programming Relaxations for Semialgebraic Problems](https://www.mit.edu/~parrilo/pubs/files/SDPrelaxations.pdf), Theorem 4.6: its equality-only specialization gives the report's certificate identity.
- Basu, [Algorithms in Real Algebraic Geometry: A Survey](https://www.math.purdue.edu/~sbasu/raag_survey2011_final-sep4-2014.pdf), Section 1.1 and Theorem 2.1: real closed fields include the real algebraic numbers, and quantifier elimination supports the stated transfer argument.

The wider bibliography is used as background and bounded prior-art context. This review does not claim an exhaustive search of the hidden-factorization literature.

## Reproduction and source validation

Executed `./checks/run_checks.sh` from the artifact directory. All **203 checks pass** under ordinary Python and `python -O`; the mathematical JSON reports match after removing the interpreter optimization flag. The 341 cylinder calculations are included in one aggregate test, not counted as 341 additional top-level checks. Tests use exact rational arithmetic and explicit failure branches. Expected values and identities are specified in the test source, not in a separate output oracle.

The test builder was checked against the report's ten residual families. Finite tests cover exact zero decoding, inactive padding and empty tuple polytopes, the stationary point, weighted local-minimum identities, a rank-budget obstruction, gradient assembly, Euler transport, and exact sublevel examples. The incompatible small-residual family is tested at epsilon = 1/2, 1/10, 1/100, and 1/1000 against the actual residual system. Its algebraic square-root slacks are evaluated exactly from rational square values, and the evaluator rejects odd powers rather than approximating radicals. Each case has exactly eight nonzero row residuals, all other residuals zero, objective 2 epsilon squared, and exact contradictions for both allowed row couplings. These tests supplement rather than establish the general proofs.

Reviewed check-source hashes:

- `checks/exact_polynomial.py`: `f31a173311b58af221d98c22d3d01cb4ce635511f3053e3501ccaa2c9a4f9cfd`
- `checks/native_encoding.py`: `c5d0150413779aa45c9d80eb7a0ab84327ebeb68b515a53b1502200b9c1844d4`
- `checks/run_checks.py`: `8f16f84f16d39c6ec6610e353d53c4a3f02a6051a9a5f2767c0a308e02b23304`
- `checks/run_checks.sh`: `a24d7b0aa5bddf295cd6895efe35380fcdd7242051e96cc1f1a10745b7985e92`

Independent structural inspection found 37 unique labels, no unresolved internal references or bibliography keys, balanced environments, and no external TeX input dependencies. The deliverable is uncompiled. No PDF or visual-layout certification is provided.
