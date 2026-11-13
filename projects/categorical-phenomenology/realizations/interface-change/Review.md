# Independent review

Date: 3 November 2026.

## Verdict and reviewed artifact

**Approved for delivery as uncompiled mathematical source. No unresolved mathematical blocker was found within the stated finite, layer-native model.**

The complete 596-line `report.tex`, including the final announcement-erasure minimum-gap proof and compositional-value-function attribution, was reviewed. This verdict applies to the exact SHA-256 fingerprint:

`f04155a56c9101abd5951ee347350e8db44c6189670864cc77905e824036c604`

The source was checked against the companion notes *Joint native realization with fixed local mechanisms* and *Fixed budget native realization and compositional gradient assembly*. The latter's compact-sublevel theorem is reused, not reproved, in the present report. Neither the review nor the finite test suite is a formal proof-assistant verification or a complete literature-priority search.

## Mathematical conclusions checked

1. **Native transport and the two resource gaps.** The supplied stochastic and deterministic squares imply preservation of the row-coupling polytopes. Transport retains the presented carrier and its total incoming mass at each state. Consequently the tensor-fibre inequality and the chain `kappa(D') <= mu_F <= kappa(D)` have the correct direction. The full-support binary example separately realizes savings from refactoring the transported tensor and savings from a newly allowed target tensor. Surjectivity between singleton tensor polytopes does not imply equality of state minima.

2. **Equality and lifting conditions.** A lawful reverse change is sufficient for equality of global native minima without requiring it to be an inverse. Fibrewise equality needs the additional stated source-tensor inverse identity. Equality between the inherited value function and the target fibre cost follows from the stronger target-tensor section condition. The observation recovery test correctly checks both `QGH=Q` and `RGH=R`. The rank-minor certificate combines an actual upper-bound implementation with a valid target lower bound.

3. **Inherited value functions.** Infimizing the source rank cost over the tensor fibres preserves its global infimum and composes by grouping the same source tensors. Empty fibres are assigned positive infinity. Finite fibre minima are attained because the feasible values are nonnegative integers. This construction is explicitly distinguished from the target's independently defined native rank cost. No convexity, differentiability, or efficient optimization conclusion is inferred from the infimum identities.

4. **Native arrows and optimizer choices.** Tensor preservation gives the correct direction and domain for the posterior comparison. The comparison span exists only in a common tensor fibre. The symmetry example correctly exchanges the two minimum-cost tensors while its unique invariant tensor requires four states, excluding a comparison-equivariant optimum choice in that example. Mutual stochastic comparisons in the occurrence-erasure example are correctly distinguished from an isomorphism.

5. **Exact-zero transport.** The core maps preserve one-hot or inactive slots and compose strictly. The bound on transported root entries uses total incoming mass per slot, not an incorrect column-stochastic assumption about the announcement channel. Nonnegative square roots give a continuous semialgebraic completion. Identity preservation is asserted only on principal-root zeros or after quotienting slack signs; it is not falsely asserted on the full signed zero set. Zero-mass active states are permitted by the actual encoding.

6. **Failure of a smooth ambient lift.** The displayed signed two-parameter family consists of exact source zeros. A core-preserving target lift would require a differentiable scalar function whose square is `r1^2+r2^2`. Its first derivative would be a linear functional with squared value equal to the Euclidean squared norm in every direction, which is impossible. This is a proof against every continuously differentiable lift with that fixed core behavior near the selected zero, not merely a failure of one square-root convention.

7. **Actual quartic loss and gradient counterexamples.** Every required residual is retained, including the two separate copies of the singleton continuation equation. Independent symbolic differentiation reproduces the output-erasure losses `5/2` and `3`, with gradients `(0,-5,0,0,0,0,0)` and `(0,-6,0,0,0,0,0)` in the stated coordinate order. The selector-merging example has source loss `1/2`, target loss zero, and a nonzero pushed source gradient. The report correctly separates these pointwise comparisons from comparisons of positive global minimum values.

8. **Positive global minimum under genuine announcement erasure.** The final budget-one proof was independently checked term by term. Eliminating the independent square slacks gives the displayed reduced loss. Taking absolute values cannot increase it: selector and cap terms are handled together, as are root positivity and gate terms; the row-distance term contracts, and the product residuals move toward their nonnegative targets. A nonnegative target minimizing core therefore exists. Splitting its root coordinate equally between the source announcements gives the exact source expression and the gate inequality. Subtraction leaves at least `1/8`, proving the claimed strict global-minimum gap. Both native problems are infeasible at every budget, as explicitly stated. The separate duplicate-module gap of at least `1/4` is also valid and does not substitute residual reweighting for the genuine-erasure example.

9. **Gradient semantics.** The report does not confuse the Euclidean transpose chain rule with forward semiconjugacy. Under a linear parameter map and loss identity, the additional `TT^T` condition is correctly necessary and sufficient along the target gradients. Linear equal-step Euler commutation is equivalent to field commutation; the corresponding nonlinear statement requires a derivative and does not imply exact Euler commutation. The increment convention for discrete assembly is stated separately.

## Input, zero, infinity, and interpretation checks

- The motivating controller is an explicitly hypothetical specification. Its fixed fairness mechanisms, observation contract, support architecture, and phase counting are assumptions, not inferred empirical facts.
- Middle-state and total-state counts are distinguished; the latter add root and terminal states.
- A zero tensor block has constrained rank zero even when its coupling polytope is empty. An unfactorable block has infinite constrained rank. A normalized feasible datum cannot have zero middle-state cost.
- Infinite native cost means no finite admissible realization exists. A finite-budget quartic always has a finite attained minimum; a positive minimum excludes that budget rather than measuring an intrinsic memory shortfall.
- The zero-budget constant is stated correctly. Unused labels and zero masses do not require surjectivity or invalid divisions.
- When a nontrivial global public output is erased, any named local public identity readouts are also coarsened as needed. Retained local rows remain fixed.

## Reproduced verification

The reviewer independently ran:

```sh
./run_exact_checks.sh
python3 check_tex_source.py
```

The final suite passed **976 exact checks** in ordinary and optimized Python, with both outputs matching the recorded expected output. The reviewed test program has SHA-256:

`a78c0acc5d04b58ab0bffa98fbbcd6bd8faf05472ce4b6816a579e497dedcfca`

The finite tests cover the specified transport squares, resource examples, symmetry, complete quartic gradient identities, exact radical samples of the zero family, and branch identities used in the announcement-erasure gap. Sampling is not used to prove the all-real minimum-gap or no-smooth-lift conclusions; those depend on their checked analytic arguments.

Static checks report 64 unique labels, 41 references, six bibliography entries and six cited keys, balanced braces and environments, and no unresolved references or missing bibliography keys. These checks do not establish compilability or page quality.

## Source attribution and limits

Independent inspection of [Hanks, Fairbanks, and Klawonn, Theorems 3.4–3.5 and Corollary 3.5.1](https://arxiv.org/html/2403.19845v2#S3.SS3) confirms the report's distinction between contravariant field assembly and forward interface transport. Independent inspection of [Rockafellar and Wets, equation 1(17), printed page 27](https://sites.math.washington.edu/~rtr/papers/rtr169-VarAnalysis-RockWets.pdf) confirms the attribution of fibrewise infimization to classical epi-composition. No novelty or priority conclusion is drawn from those checks.

The added [Stein–Samuelson attribution](https://arxiv.org/html/2312.02291v2) was checked against Sections 3 and 4.3: composing convex bifunctions uses infimization over shared variables, and discarding decision variables produces value functions. The report explicitly does not import convex closure or duality claims into its nonconvex rank and quartic problems. The [publisher record](https://doi.org/10.1007/978-3-031-57228-9_9) confirms FoSSaCS 2024, LNCS 14574, pages 166–187.

**Rendering limitation:** the saved compiler output reports a missing `pdflatex.fmt` installation. No PDF was successfully compiled, and no visual page verification is claimed. The review approves the mathematical source and the disclosed verification record, not rendered typography.
