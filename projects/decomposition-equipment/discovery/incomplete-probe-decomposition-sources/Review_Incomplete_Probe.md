# Independent adversarial review: incomplete-probe directional discovery

Reviewed 2026-10-28. This is an independent mathematical/code review, not Lean verification, external peer review, or a novelty determination.

## Verdict first

**The principal exact-population theorem is sound within its stated affine shared-effect universe.** It discovers a nontrivial task quotient from observed baseline and paired residual tables without identifying a shared latent frame. The matrix-atlas equations then preserve genuinely shared uncertainty through positive assembly. The conditional eight-state fixture exercises this claim rather than merely accepting a supplied quotient: it discovers four states from randomly labelled raw states, while no autonomous task quotient exists.

The result does **not** establish unrestricted readout-to-physical-architecture discovery. Candidate measurement patches, a bounded affine source universe, full response-partner rank, and sufficient joint context coverage are substantial premises. A new integrated fixture learns unknown noisy sensor channels from exact observation-law tables; no sampled finite-data implementation accompanies it. These limits must remain in the abstract and completion claim.

The vector theorem now explicitly includes the necessary qualification: conditional one-step quotient closure does not itself prove closure of a quotient-plus-persistent-source process when the source transition depends on discarded microstate. Retain the residual fiber, or impose the necessary source-transition factorization. This is not a blocker to the one-step theorem or the IID-source stress family.

## What was checked

Read `main/Vector_Directional_Theorem.md`, `main/Directional_Quotient_Discovery.md`, `gluing/Matrix_Atlas_Classification.md`, and `stress/Matrix_Gauge_Family.md`. Inspected the conditional-core and directional-refinement scripts. Independently reran all seven scripts successfully:

- `main/check_directional_refinement.py`
- `gluing/check_matrix_atlas.py`
- `gluing/check_shared_algebra.py`
- `stress/check_matrix_gauge.py`
- `stress/check_discovered_core.py`
- `stress/check_conditional_core.py`
- `stress/check_noisy_conditional_discovery.py` (default plus five-seed run)

These are bounded numerical/algebraic regression checks. They do not by themselves prove general statements, statistical consistency, or novelty.

## 1. Identification of the response space

Conditional fresh-noise independence and conditional source moments E[Z]=0, E[ZZ^T]=I give the centered pair table D_ij=F_i F_j^T. If F_j has full column rank r, multiplication by F_j^T is surjective onto the r-dimensional latent coordinates; therefore range(D_ij)=range(F_i). Full rank F_i additionally makes the local coordinate matrix invertible and supports the subsequent GL(r) classification.

This argument is correct for the flattened matrix only if every displayed pair of contexts belongs to the same declared conditional moment regime and the required table entries are available. Separate marginal coverage does not furnish joint Cartesian coverage. Conditioning on noisy old-state estimates rather than truly calibrated latent-context tables does not automatically satisfy the equation.

**Important assumption accounting:** this removes the earlier requirement that a regime probe separate all latent source states. It does not remove relevance/completeness-like assumptions altogether. A source direction that affects only one patch, or every available partner rank-deficiently, can remain invisible in the pair residual. A zero observed residual is not a general certificate of no hidden bypass. The notes correctly exclude omitted effects outside their declared affine universe. The report should say this directly rather than calling the result assumption-free incomplete-probe discovery.

## 2. Coarsest conditional quotient and autonomy

Let U be any basis of range(F). Equality of the aggregate contrast rows on U is equivalent to equality on F, since the change of coordinates is invertible. Thus the proposed refinement test is independent of the unresolved gauge. The finite partition-refinement proof is valid: every valid task quotient refines the initial task partition, and block summation preserves the induction after each split. The stable partition is therefore the unique coarsest valid deterministic task quotient.

The separate autonomy condition is also correct. If any quotient block has nonzero aggregate contrast, every autonomous task quotient would refine the discovered conditional partition, and summing its zero-contrast blocks would give a contradiction. Conversely zero aggregate contrasts leave an effect-independent response. Covariance I ensures the admitted source support spans the latent directions, preventing a nonzero linear contrast from being harmless on all admitted effects.

This is an exact conditional-kernel result. It does not give the controller exact access to the latent effect or calibrated hidden patch state. It does not prove minimal physical memory among all stochastic encodings or alternative timing architectures.

## 3. Boundary and persistence

The input-boundary construction is sound as finite-state transducer minimization after a specified finite input-history update algebra is given. Both baseline and contrast signatures must be retained. Starting from response equality and refining to a transition congruence gives the coarsest deterministic recursively maintained summary under those fixed update/initialization rules. It is not a general inference theorem for arbitrary unbounded histories.

Accessible input symbols and register initialization must be charged. A generative latent-state quotient is not an online observable controller state merely because sensor channels are identifiable.

For persistent source uncertainty, distinguish three claims:

1. Pointwise conditional quotient rows are well defined.
2. The full whole process, retaining residual state and source memory, has a positive coherent realization.
3. The reduced quotient together with a reduced source state is dynamically closed.

The first two do not imply the third. If a source-memory transition reads discarded old microstate, the residual must remain or an additional factorization hypothesis is required. The existing shared-algebra regression contains the relevant counterexample pattern. The main author added this qualification explicitly in §7; it resolves the review concern.

## 4. Matrix graph classification and positivity

The spanning-tree derivation is correct. With root factor H, alternating parity gives A_i=L_i H or L_i H^{-T}. Opposite-parity chords impose root-independent matrix identities. Even-even chords impose a common S=HH^T, odd-odd chords its inverse. A nonbipartite connected graph therefore requires mutually compatible SPD constraints and leaves H=S^(1/2)O. A bipartite graph leaves arbitrary H in GL(r) before positivity.

The distinction between algebraic feasibility and stochastic positivity is essential and correctly retained. A common admissible H must make every local row nonnegative for every admitted source atom and context. Arbitrarily combining individually admissible local choices can violate the edge equations or global positivity. The code exercises both a four-cycle inconsistency and a non-SPD triangle.

A fixed finite non-rotation-invariant source law makes orthogonal freedom physically substantive: preserving all pair moments need not preserve fourth moments. It is harmless coordinate freedom only when the source law and dynamics are transported too, or the transformation is an actual source symmetry.

## 5. Whole realization and temporal observation scope

One common source draw per update, one globally fixed mechanism gauge per world, and conditionally independent fresh local outputs provide a positive normalized whole transition. Refinement/regrouping must reuse the same source occurrence. Resampling a gauge per component/time would incorrectly replace shared-world uncertainty by rectangular uncertainty.

The pair-history statement is correctly restricted in the current notes. It requires closed projected contexts, equal initial pair laws, and policies using only those histories and permitted inputs. Conditional first and second moments given the full past permit induction even when higher moments have persistent uncertainty. Unconditional moment matching alone would not suffice. A policy observing other masks or an unobserved neighbor entering the next-state kernel invalidates the unrestricted pair-history argument.

The stationary-pair observation in the positive IID stress family is valid: the autonomous pair kernel is positive, has a unique stationary law, and every stationary whole law projects to it.

## 6. Does the example really discover anything?

The stronger conditional fixture does. Its learner receives raw labels, task signature, B, and D; it does not receive the (a,b) quotient. It searches 225 task-preserving partitions, obtains two conditional partitions (the four-state core and eight-state identity), proves the four-state one coarsest by direct refinement comparison, and finds no autonomous partition. Pointwise hidden-source validation is performed after discovery. Minimum raw probability is approximately 0.0258583.

The initial task partition itself has zero source contrast but fails baseline lumpability; refining it forces a retained state distinction with nonzero source contrast. This concretely distinguishes task-level average cancellation from a functioning autonomous component. The joint ambiguity therefore lives in the useful discovered core, not merely in discarded nuisance.

However, a supplied candidate patch cover and a specially structured affine hidden-source model remain. The fixture does not discover physical sensor ownership, arbitrary component topology, or arbitrary unknown effect channels. Nonlinear within-patch feedback and common-cause coupling are present; direct cross-patch causal feedback is not part of the all-pair-history indistinguishability proof. These are scope restrictions, not algebraic defects.

## 7. Statistical and sensor qualifications

The stated subspace perturbation bound is valid: if ||Dhat-D||<=epsilon and rank(D)=r with smallest nonzero singular value s, truncated rank-r projection gives ||Phat-P||<=2epsilon/s. Aggregate-functional score bounds follow by operator norm; baseline block errors follow by summation. Separation margins permit stable thresholding of the finite list of equality decisions.

This is conditional numerical stability, not an end-to-end sample theorem. Obtaining the assumed table errors needs calibrated sensor inverse conditioning, latent-label alignment across times/contexts, support floors, and a valid concentration argument. The original scripts begin from exact population conditional tables. The added standalone noisy-sensor fixture instead begins from exact observable probability tables and learns the sensor channels before deconvolution. Neither approach establishes performance on finite sampled observations or that arbitrary persistent sources mix rapidly. The new §8 imports precise inverse-conditioning assumptions for a conditional finite-observation guarantee.

The fourth-moment gap at the small displayed amplitude is extremely small. The stress note properly charges this and does not claim economical experimental distinction. Fixed local dimension makes table algebra scale favorably with the number of patches; it does not make positivity feasibility, context acquisition, calibration, or weak-signal statistics generally cheap.

## Release recommendation

Release as an exact structured theorem for **gauge-invariant conditional quotient discovery and coherent positive assembly under incomplete shared-effect observations**, with the now-included persistence caveat and the exact-observation-law status visible. Do not present it as completed physical architecture discovery, general bypass certification, a finite-data implementation, or a new matrix-factorization mechanism. Keep the stronger same-mode paired-replica alternative secondary: its experimental-access promise is materially stronger than ordinary simultaneous distinct-patch observations.


## Final addendum: reviewed §7/§8 and integrated noisy-observation fixture

**Accepted after independent inspection and rerun.** §7 correctly distinguishes one-step conditional closure from persistent quotient-source closure and explicitly charges residual fibers/messages. It also specifies the finite input-register update assumption.

§8's Hoeffding/union-bound sample count is correct: Q tables with at most J cells and cell error delta/J require N >= J² log(2QJ/alpha)/(2delta²) independent samples per table. The fit-to-truth factor two, conditional imported inverse-Lipschitz sensor bound, telescoping inverse-factor bound, simplex-fit factor two, context normalization bound, and residual bound 3nu are valid with the stated fixed norm/conditioning conventions. The result assumes a finite calibration inverse constant, stable ranks/labels, context floors, and separation margins; it does not derive those promises from generic randomization. It is a conditional finite-sample lemma, not a concrete implemented learning-rate result with numerically evaluated constants.

The new `check_noisy_conditional_discovery.py` generates an actual positive stationary 64-state pair chain and unknown 10-by-8 sensor matrices, then exposes only observable three-view tables, a 10^4-entry old/next sensor tensor, and sensor/task joint tables to the learner. The learner estimates sensor channels spectrally, deconvolves the temporal tensor, normalizes context rows, obtains B and D, learns task-emission levels, and searches task-preserving partitions. Hidden K, F, state coordinates, the true stationary state weights, and the true quotient are not used to compute those learner outputs. Hidden-label alignment and comparisons to true kernels occur afterward only for validation.

The supplied patch count, finite-state/independent-sensor model class, stationary-law setup, and exact observable probability tables remain premises. The code does not simulate finitely many noisy records; “noisy” refers to the nontrivial unknown observation channels. There is no latent-state preparation or same-mode replica access in this fixture.

Default and five-seed runs passed independently. Every run learned two eight-state alphabets and two uniquely coarsest four-state conditional quotients, with zero autonomous task quotients. Across five seeds the largest validation-only conditional-kernel error was approximately 8.27e-13. The default minimum recovered stationary context mass was approximately 0.00360832. This closes the prior *population-law calibration integration* gap, not the remaining finite-sample implementation gap.
