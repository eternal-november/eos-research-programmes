# Independent review: partial subsystem discovery

Review date: 28 October 2026. Reviewer: independent parallel AI proof review, not Lean or external human verification.

## Verdict in plain language

**Accept the population-law theorem within its explicitly declared universe.** It discovers a task-preserving state quotient and an incoming boundary rather than receiving the desired subsystem as input. It does not reconstruct the unseen surroundings. However, it assumes a complete bounded description of how those surroundings can affect the patch and a randomized experiment that separates those effects. It does not learn that experimental promise from passive data.

The result is an inward-autonomous generative subsystem, not a sealed physical replacement or a robot safety guarantee. Current finite-data discussion is a list of sufficient statistical obligations, not an implemented finite-data discovery pipeline.

## Materials checked

Read main/Partial_Subsystem_Discovery.md, exterior/Exterior_Closure_and_Feedback.md, stress/Unobserved_Exterior_Family.md and inspected the three associated scripts. Re-executed all three scripts with OPENBLAS_NUM_THREADS=1: all passed. Main refinement checked 225 task-preserving partitions; stress noisy-law discovery checked N=2,3,5 exterior sizes. These are numerical exact-law fixtures, not proof of all-size product separation or finite-sample guarantees.

## Resolved substantive defect

The first draft's coverage language could have allowed training correlation to masquerade as a sufficient input. If training U=V and next Y depends on V, both singleton contexts can have full support and zero conditional entropy. Selecting U fails when a new exterior breaks U=V.

**Repair verified in the written main note:** every pair-union of candidate contexts, jointly with old X, has Cartesian support (at most 2k slots), or the arbitrary-input-policy claim is withheld. This upgrades the entropy/KL almost-sure identity between selected A and true A_* to pointwise equality. Separate marginal coverage is explicitly ruled out. This is a substantive stronger assumption and must remain visible in the report.

## Proof checks

1. **Probe lemma:** valid. R is randomized after all conditioned variables. For the unknown sufficient context A_*, the observed regime difference is the fixed response contrast multiplied by E[p1(H)-p0(H)|X,w], at least delta. Independence also implies genuinely closed responses pass every coarser preprobe-context test. Completeness of F(X,w,Z) is essential; extra H-dependent response vectors could cancel.
2. **Missing observed parents:** handled separately, correctly. Probe invariance alone does not detect omitted measured inputs. Entropy minimization occurs only after hidden-mode closure and includes the unknown sufficient bounded context. Pair-union support is needed for policy changes.
3. **Task-preserving refinement:** valid induction. Every valid task-preserving partition refines every forced split; a mode-sensitive current block obstructs any finer valid quotient because its probabilities are sums of finer-block probabilities. Termination yields the coarsest valid quotient of this fixed X, not a maximal subsystem across arbitrary state memories or sensor patches. Unequal fibers are legitimate.
4. **Boundary recursion:** ordinary finite-state congruence refinement gives a causal finite-history register preserving the response table. This does not optimize all possible state/interface tradeoffs. Its direct implementation assumes actual access to its input symbols; the latent-port variant is only generative.
5. **Whole-law lifting:** disintegration gives a positive dependent-fiber realization. Full quotient state, including initialization and new state each round, is explicitly charged to the remainder. This is not evidence that the physical world has that wire or only that outward interface.
6. **Joint closure:** correctly not inferred from marginal closure. The correlation-changing counterexample is strictly positive and effective.
7. **Feedback:** pointwise uniform response control supports adaptive-history coupling with initial-law error plus H times per-round error. Different exterior input policies do not produce identical unconditional trajectories; the notes state this distinction. Finite horizon and observable outcome scope remain necessary.
8. **Temporal sensor recovery:** revised main note explicitly requires conditional independence across sampled times given the latent path. Within-time three-view independence alone would not suffice for temporal tensor inversion.
9. **General exterior rank lemma:** correct for the stipulated conditional matrix or conditional expectation operator. Conditional soft-tilt rank is valid as written; it must not be inferred merely by averaging unrelated hidden-history-dependent soft-tilt families. Exact rank can be statistically ill-conditioned, as QA demonstrates.

## Stress-example qualification

The noisy stress example is not an unqualified direct accessible-port instantiation. Raw patch P2=(b,v) shares b with X=(a,b,y), so Cartesian support of raw X and P2 fails. Its written separate product-chart/overlap procedure discovers a latent port quotient v; the generic Cartesian theorem can apply only after the appropriate coordinate/access/support conditions are established. The fixture also does not implement the entire generic context-enumeration algorithm: the main known-kernel refinement QA and the noisy observation-law stress QA exercise different parts of the argument. Neither should be labeled an end-to-end finite-data implementation.

The stress note correctly says latent v is not decoded noiselessly online and charges delay at the generative level. Keep this distinction in the user report.

## Remaining gates and accepted scope

- No unresolved blocker to the **population theorem as revised**.
- Any finite-data wrapper added after this review requires its own check; current qualifications alone do not establish explicit sample complexity.
- Structural effect completeness, intervention exclusion/separation, calibration, sparse sufficient input bank, and support are promises, not simultaneously certified world-membership facts.
- The main theorem searches deterministic quotients of a bounded calibrated patch; it does not solve unrestricted unknown architecture discovery.
- Standard mechanisms include latent-mixture recovery, randomized invariance, controlled lumpability, congruence minimization, and conditional disintegration. Their integration and precise discovery/access scope are the candidate contribution; novelty is not proved by this review.
- No discharge of the original research contract, physical safety theorem, or general bidirectional replacement claim follows.

## Addendum: conditional finite-data theorem (23:02 UTC)

Read and accepted main/Finite_Data_Stability.md after its observation-scope correction. The appendix supplies a conditional finite-sample theorem, beyond the original main note's qualifications: compact calibrated inverse charts give an implicit finite inverse constant; bounded-table tensor inversion, simplex projection, and conditioning propagate one-norm error; uniform probe, entropy, task-signature and response gaps recover the population decisions. The near-minimum entropy band uses the correct two-sided error allowance. Coordinate Hoeffding with a union bound is valid for the expressly assumed independent windows; arbitrary exterior memory does not imply this sampling premise.

The finite constant is not numerically evaluated, minimum-distance calibration is a mathematical estimator rather than an implemented scalable optimizer, and the fixture is still exact-law numerical QA. Thus conditional statistical existence is accepted, not practical sample feasibility.

The final paragraph now correctly limits H*e/2 retained-transcript error to the same causal policy on that transcript and an observation channel factoring through the quotient/boundary. Full-patch sensors need not do so. A whole lifted comparison requires common conditional remainder kernels and initial residual law; a policy using omitted private information requires a common coupled extension. This resolves the only additional scope issue found in the statistical appendix. No remaining blocker in the stated population or conditional finite-data results.
