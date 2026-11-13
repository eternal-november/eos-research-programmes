# Independent review of causal evidence and executable observer proofs

29 October 2026. The main proof notes and stopping example have been read in full. No unresolved substantive mathematical defect was found in the statements at their declared scope after the repairs recorded below. This is independent AI review, not Lean or human verification and not a novelty clearance.

## Causal law representation and target policy change

The finite causal polytope uses prefix action-randomization equalities, not only action marginals. Its converse realization proof is correct: define environmental conditional rows from positive prefix probabilities and choose arbitrary stochastic rows at zero prefixes. Under target action-support coverage, a target-positive prefix is also exploration-positive. Hence arbitrary rows on zero prefixes do not change the target law.

The likelihood-ratio objective is now explicitly fixed by the two policies and the trajectory. It is not redefined according to a candidate probability law. Zero exploration-policy denominators receive weight zero because coverage excludes target mass; zero candidate probability with positive denominators does not alter the fixed coefficient. This clarification is important for the linear-programming formulation.

The causal constraints describe an admissible experimental law class. They do not establish physical exogeneity, unchanged environmental response under intervention, or deployment stationarity from observational frequencies. The proof and final claim must retain those assumptions.

## Quantitative assurance and statistical event

For a nonempty confidence polytope, the displayed finite LP dual has the correct signs: upper multipliers are nonnegative, lower multipliers enter negatively, and equality multipliers are free. Weak duality follows pointwise and strong duality supplies an attained optimum for the bounded nonempty primal. Empty feasible families are rejected rather than used for vacuous assurance.

The upper physical decoder and its error budget are separate from statistical confidence. A high upper-surrogate score does not prove actual unsafety. A necessary-unsafe conclusion needs the separate lower transfer contract. Physical-risk uniformity concerns environments satisfying those transfer contracts; an observable law alone does not assign the missing physical hazard semantics.

The iid bound applies to independent whole episodes from the same population, allowing arbitrary dependence inside each episode and between features. It is not a bound for time points in one dependent record. The current note explicitly rejects unmodeled cross-regime pooling and outcome-selected missingness. Simultaneous feature coverage, or a separately valid held-out/complexity argument, is needed for postselection. The countable prefix-code weighting extension is a valid union-bound construction; it does not make unseen features measured or unbounded synthesis decidable.

Exact rational checking and conservative outward rounding are appropriately separated from floating solver tolerances. Policy coverage can make likelihood ratios exponentially large in the horizon; no hidden finite-sample efficiency is inferred.

## Necessity and informative failure

The row-span criterion is correct under the stated strictly positive point on the supported affine slice. Failure supplies a kernel direction and two sufficiently small positive/negative perturbations with identical retained population information but different risk. Forced-zero support and extra affine restrictions must first be removed or represented; the note states that correction.

The added threshold-adequacy LP is also correct: maximize the high-score side above alpha while imposing an equal-feature low-score side. A positive optimum is exactly a threshold-straddling fibre; nonpositive optimum means the verdict is constant on every feature fibre. This is weaker than exact numerical risk determination and does not unnecessarily require row-span reconstruction. An infeasible low-score side is handled separately.

Finite confidence-band membership alone is not observational indistinguishability. Two compatible laws may become distinguishable with more data from the same observer. The exact paired-law LP imposes equal retained feature expectations; its conclusion is relative to those features, not every possible statistic of the original archive. A risk difference also need not cross the requested threshold.

Finite row-addition terminates because each excluded maximizing law violates a previously omitted available row. It does not promise minimum cost, cheap search, or success under a budget that prevents acquiring the needed observer family. An adverse law admitted only after evidence deletion diagnoses representation loss; a law in the full evidence family diagnoses current evidence insufficiency. Neither necessarily identifies the actual environment.

## Executable observer semantics

The source syntax includes actual time/owner permissions, old-memory delays, channels, registers and shared physical identifiers. Its typed circuit maps compose, and their evaluations on one common trace give the claimed pushforward identities. Parallel report laws are joint pushforwards, not products of separate marginals. The final note distinguishes a circuit map on its input record carrier from its restriction to environmental trajectories, avoiding an untyped composition of two maps with the same domain.

The observer's output law supplies evidence rows only when those outputs were actually acquired or can be replayed from aligned archives. An observer compiler cannot reconstruct a missing joint distribution from unaligned marginal counters. Executability also does not prove hardware attestation or physical noninterference: logging may change latency, energy or bandwidth. The note now states that such effects require a different modeled protocol or justified invariance contract.

For a fixed risk potential, factorization through a coarser report is exactly constancy on adapter fibres over the claimed carrier. Restricting to reachable outputs requires a justified image restriction. This is a transport test for the fixed potential, not a proof that every alternative risk certificate fails when this one does. Retaining the old aggregate confidence bound or deriving a new one is necessary.

The one-message response-row theorem is correct on a full product sender/receiver support. Its minimum alphabet count is the number of distinct response rows, and the threshold example requires K+1 symbols. Correlated support, extra sensing, or a prior query phase changes the problem; the note explicitly distinguishes those cases.

## Stopping interaction examples

The stopping envelope is a conditional physical upper bound. The amended distance convention uses an allowed stopping distance strictly inside physical clearance, avoiding equality/contact ambiguity. The binary and triple numerical examples are mathematical calibrations, not recommended operating parameters.

The triple-moment family is correct: all compatible laws have parameter q in [0,1/100], with hazard probability 3/100-2q. The pointwise risk identity using three pair products minus twice the triple product is exact. The interval majorant 0.016+5 epsilon yields 37/2000 at epsilon=1/2000. Its large Hoeffding sample demand is honestly stated.

The separate 300-record zero-event example is explicitly constructed hypothetical evidence. The simultaneous one-sided zero-event bound over at most seven predeclared statistics is valid, with exact rational outward certificate 17/1000. It becomes an assurance example only after valid aligned deployment-relevant data exist. A direct joint hazard counter can be simpler than retaining a full joint table; this is correctly acknowledged.

The recurrent parity example initially overgeneralized a fixed-patch claim. It is repaired: for rho>0, each FIXED proper-coordinate history law agrees between parity classes, but changing patches over time or aligning overlapping patches can reveal parity. The no-information statement is now restricted to separately sampled unaligned fixed-patch histories. At rho=0, fresh vectors within a persistent parity class also hide the class from adaptive selection of one proper patch per time, provided same-time patches cannot be combined. These are distinct acquisition protocols.

## Independent exact checks

Two independent standard-library scripts are supplied:

- tests/review_causal_policy_and_evidence.py: 4096 exact two-step policy-change models with non-Markov observations and a persistent hidden variable; controls for action confounding, equal marginals with opposite risk, postselection coverage loss, and shared versus rectangularized uncertainty.
- tests/review_quantitative_interactions.py: 29 exact risk-identity and moment checks, 18 fixed-patch history comparisons, and an explicit switching-patch counterexample. For rho=1/2, the same switched observation event has probabilities 3/16 and 1/16 in the two parity classes despite equal fixed-patch histories.

The author's causal-risk and executable-observer scripts were also rerun and passed. These finite checks corroborate proofs but do not verify every unbounded horizon, actual sampling process or physical interface.

## Final scope

This construction gives conditional, finite-horizon behavioral assurance across a shared evidence-compatible law family, with executable observer witnesses and quantitative missing-information diagnostics. It does not identify physical subsystem mechanisms, guarantee arbitrary unmeasured hazards, prove noninterference of installed hardware, make exponential pathspace or constraint width disappear, or finish the original operational/C5 interpretation. The underlying LP, policy-change, contextual/communication and concentration mechanisms are established mathematics. The programme contribution must be stated as their explicit certificate/observer integration rather than a new general identification mechanism.

## End-to-end implementation supplement

The independent reviewer read and reran tests/check_end_to_end_discovery.py and read examples/End_to_End_Observer_Discovery.md after the core proof review. All checks passed. The uniform exact binomial inversion at delta/16 for all sixteen Boolean event functions gives simultaneous coverage despite subsequent selection; complementary output events do not increase the family beyond sixteen. Outward rational rounding is conservative. The exact bounded-polytope vertex search and exhaustive one-way encoder/decoder synthesis validate the stated small pipeline. Only AND and NAND succeed with robust surrogate risk 39/2000 versus the local-only 313/2000. Nine-bit count memory is separate from the one-bit report alphabet. Existing aligned replay, prospective distributed acquisition and missing joint data are correctly kept distinct. See Final_Report_Scope_Audit.md for hash-bound final artifacts and scope.
