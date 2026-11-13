# Independent review of dynamic product atlas discovery

Reviewed on 2026-10-28. This is independent AI mathematical review, not Lean verification or external peer review. The review concerns the population construction, explicit error-transfer statements, and positive atlas gluing, not a claim of scientific priority.

## Main conclusion

The population identification pipeline and the exact local-to-global transition theorem are sound under the declared finite-state, positive, independent-innovation, full-rank three-view observation universe. They remove a supplied one-coordinate-per-port correspondence and do not require the observation overlap cover to expose every component. The construction remains a structured-family theorem, not a test of arbitrary physical-world membership.

The review found one substantive finite-data selection issue: choosing the smallest exact empirical entropy minimizer need not recover the essential parent set, because sufficient supersets tie in population but generally do not tie empirically. The repair is to retain an error-controlled band of near-minimizers before minimizing cardinality. The author incorporated this repair in Section 9, and it was rechecked. Smaller scope clarifications were likewise incorporated. The final compact-calibration sampling wrapper was separately reviewed below.

## Population steps checked

1. **Three-view calibration.** The pair-marginal rank identifies the unknown hidden patch cardinality under positive weights and full-column-rank emissions. The simultaneous-diagonalization identity is correct. Column stochasticity removes eigenvector scaling, leaving a common patch permutation. A finite deterministic set of contractions can replace open-ended rational search: for sensor alphabet size s, use z(t)=(1,t,...,t^(s-1)) at more than C(R_p,2)(s-1) distinct t values. Each pair of emission columns coincides on at most s-1 such contractions.

2. **Joint deconvolution.** Tensor products of left inverses are justified by conditional independence of sensor noise, not independence of hidden patches. Overlapping hidden patches are therefore permitted. Reusing the same sensor draw as independent observations would not be justified; the declared protocol excludes that error.

3. **History support.** Every consistent cylinder specifying k coordinate-time values has probability at least kappa^k. Order the prescribed times, condition on the preceding hidden history, and integrate unspecified values. This remains valid under stationary initialization. Duplicate prescriptions must be counted once, and inconsistent overlapping prescriptions have probability zero.

4. **Context discovery.** Every candidate old-patch context is a function of the full lag history. Conditional entropy is bounded below by conditioning on that history. A context covering all true parents attains the bound. Hence every exact population minimizer is sufficient for the full next-patch conditional law. This inference does not assume that the learner already knows the parent coordinates.

5. **Dynamic coordinate recovery.** Equality of additive function spaces determines the product-of-simplices evaluation polytope and hence its coordinate directions. The triangle/opposite-induced-square edge relation correctly recovers directions, including binary factors. The separate polynomial unique-factorization proof of universal product-preserving recodings is also correct for differing input/output factor shapes. Its generic single-row conclusion is a finite-union algebraic avoidance result, not a uniform quantitative margin or an automatic statement about a constrained dynamical parameterization.

6. **Alignment and parents.** Full latent support distinguishes a repeated atom's matching support from distinct atoms' full Cartesian support. Essential parent coordinates are uniquely determined by dependence of the recovered kernel under full support. The identifiable target is the finest admissible conditional-innovation coordinate structure, not an arbitrary originally assigned grouping of physical parts.

## Global gluing checked

The coherent-atlas support argument is valid: pairwise equality constraints determine the full compatibility space because the declared hidden support is an unconstrained product. This would fail for parity-constrained or otherwise globally restricted latent support; the note explicitly excludes those cases rather than pretending pair data rule them out.

For a coherent candidate atlas, the transported true transition log-density is a sum of patch-supported terms. The proposed product transition also has that form. Equality of every full next-patch marginal therefore makes the expectations of their log-density ratio equal. The difference equals the sum of the two directed KL divergences, so the whole transition distributions agree. This is a valid positive exponential-family argument, not a generic claim that pairwise marginals determine joint laws.

The approximate version is also correct. An expectation difference is bounded by oscillation times total variation, so no extra factor two is required in the displayed sum of local log-probability bounds. Pinsker then gives the stated square-root global bound. This bound grows with the number of atoms and requires uniform conditional local errors.

The unresolved-family completeness claim is valid relative to the patch-compatible observation universe and the explicitly enforced resource bounds. It does not include extra invisible states or arbitrary alternative sensor grammars. Candidate patch-width, parent, delay, and positivity bounds must be checked if membership in the original bounded universe is claimed. A coarsening can reduce transition probabilities from kappa to kappa raised to a power; truth and candidate positivity floors must not be silently identified.

## Interfaces and initialization checked

Controlled partition refinement gives the coarsest deterministic strongly lumpable quotient refining the prescribed outgoing responses. Its lower bound is only for that fixed state-summary/input/output/timing contract. It is not an unconditional hardware-memory or arbitrary-protocol lower bound. Shared source/summary outcomes must use the same next-state draw.

The crossing example is correct: R and R xor H are separately fair one-bit summaries, while their joint future law depends on hidden Z. Old joint summary state has four values, and the required deterministic refinement has eight. This is an obstruction to an autonomous joint summary under the stated budget, not to every possible common realization with extra hidden state.

The initial memoryless Dobrushin formulation needed a lag qualification. The revised fresh-update bound is correct: if the total parent-lag influence into each fresh coordinate is at most kappa<1, the maximum mismatch probability over the previous L times contracts by kappa after L updates. A union bound gives |B| L kappa^floor(T/L) on the full lag history. Adding T beta for a uniformly approximate fresh transition gives the stated model burn-in bound. This is simulated initialization, not control of the actual environment.

## Finite-data repairs and limits

The explicit inverse, simplex-projection, conditional-row, minor, partition-refinement, and product-coupling bounds are conservative and valid as written. Valid probability projection is necessary because empirical spectral inversion may produce negative entries.

Let E bound the error of every candidate conditional entropy and Delta be the gap from sufficient to insufficient parent sets. An empirical point minimizer is sufficient when Delta>2E. To recover the *smallest* sufficient set, retain every candidate within tau of the empirical minimum, where 2E<=tau<Delta-2E, then choose minimum cardinality. This requires Delta>4E. Without this step, empirical overfitting can favor a redundant parent even though all insufficient sets are separated.

Define the entropy continuity modulus at alphabet size one to be zero; empty contexts and constant latent patches otherwise make log(M-1) undefined. Empty patches require the empty Cartesian profile or explicit removal after calibration.

The final manuscript strengthens the local transfer argument with a uniform compact-calibration wrapper. This is valid, for the following reasons. Full-rank emission matrices and positive mixing weights give a pair-marginal singular-value gap at least pi0 sigma^2. For each parameter point, a finite choice of invertible row/column minor and a separating moment-curve contraction gives an analytic inverse branch modulo hidden labels. Spectral projectors and nonzero stochastic normalization make that branch explicit. A finite compact cover bounds local inverse derivatives. A compact separation argument for pairs outside these neighborhoods extends the bound globally modulo the finite permutation group. Mere injectivity and compactness would only give uniform continuity; the analytic local inverse construction is the additional needed ingredient.

A minimum-distance fit in the compact valid parameter class has forward error at most twice the raw-table error and hence parameter error at most 2 C_cal delta. An approximate optimizer must add its residual tolerance. The displayed pseudoinverse perturbation estimate follows directly by the inverse-Gram identity, using both fitted and true sensor singular-value floors; it does not need an interpolation path that stays full rank. The final independent-window Hoeffding and union bound is then valid for all potential bounded masks, including calibration and adaptively selected queries.

This establishes a finite-sample theorem with a defined fixed-conditioning constant and a mathematically specified estimator. It does not numerically evaluate that constant, demonstrate a practical optimizer, give a finite-sample experiment, or establish polynomial dependence on every conditioning parameter. These distinctions are explicit in the manuscript.

## Limits of this review

The all-size mathematical arguments, rather than the finite numerical tests, support the theorem. The numerical scripts are separate regression evidence. No conclusion here identifies physical hardware uniquely, grants a controller access to hidden state, proves safety for unmodeled hazards, or discharges the original virtual-equipment research contract.
