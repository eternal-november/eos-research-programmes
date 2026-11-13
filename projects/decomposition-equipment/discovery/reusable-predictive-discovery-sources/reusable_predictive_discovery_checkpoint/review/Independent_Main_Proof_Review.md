# Independent proof review: recursive predictive discovery

29 October 2026, review of `theory/Robust_Recursive_Predictive_Discovery.md`, `theory/Positive_Joint_Realization.md`, and the two service-family example notes. Independent AI review, not human review or proof-assistant verification.

## Plain-language abstract

The principal proof works within its stated finite-horizon resource contract. It converts a difficult comparison of complete predicted trajectories into a check of joint next-step errors weighted by the actual possible environment histories. This error measure is not arbitrary: it bounds full-record prediction error and is zero exactly when the complete laws agree. Its special form permits a linear optimization for each proposed recursive implementation. The result still faces large computational costs, and the current small example is population-table calibration rather than a successful finite-data architecture-discovery benchmark.

## 1. Main theorem audit

### 1.1 Transfer bound

Let P be the true fixed-world law under a fixed allowed controller and Q the proposed simulator under that same controller. Both live on the entire raw history tree. At every step, the controller's action kernel is a common stochastic map. The predictor's output kernel is also a common map on raw histories, even when it accesses only a compressed, recursively maintained state. Therefore the triangle inequality comparing P_next, P_prefix K and Q_prefix K gives the advertised accumulation under TRUE prefix occupancy.

No predictor-state Markov property for the actual environment is needed. No comparison between conditional probabilities at zero-mass prefixes is needed. No independent choice of the actual environment transition at different histories occurs. The bound Delta<=min(1,J) is sound.

### 1.2 Reverse bound

The identity

    E_Pprefix TV(P_next(.|prefix),K(.|prefix))
       = TV(P_next,P_prefix K)

holds on positive prefixes, with zero prefixes contributing zero. Triangle inequality through Q_next and contraction under K then bound each term by twice full-law TV. The initial term contributes at most one further full-law TV. Summing proves J<=(2H+1)Delta. Supremizing over the same fixed pairs (p,pi) is legitimate.

This establishes exact equivalence at zero discrepancy and a horizon-dependent approximate completeness guarantee. It does not establish equal conditional predictions at histories neither law visits. It is not an infinite-horizon estimate.

### 1.3 Finite LP

For a fixed executable program and fixed response mixture, J_(p,pi) is convex in the exploration-law vector p. Its maximum over the confidence polytope is attained at a vertex; candidate-dependent conditional normalization has been avoided correctly. For fixed p and K, maximizing J over the rectangular full-history policy family is an ordinary finite history-tree control problem with deterministic maximizers. Nonnegative absolute-value slack variables give exactly the claimed epigraph, not a relaxation.

The use of confidence-polytope vertices is potentially prohibitively expensive but mathematically valid. It does not rectangularize environmental uncertainty: each vertex remains one full causal law through every residual term. Replacing these vertices by independently extremized conditional rows would be a different and generally weaker theorem.

### 1.4 Program discovery and statistics

Finite enumeration plus exact LP solves the declared finite language, including unknown program choices. This is completeness relative to the resource syntax, not a tractability result or a completeness theorem for all physically executable systems. Shared-source support restrictions must be enumerated or otherwise imposed exactly; unrestricted LP support does not enforce a smaller source budget.

The post-selection claim is valid when the SAME confidence set has simultaneous true-law coverage before selecting programs/controllers. Adaptive creation of evidence features must itself have valid coverage. The theorem correctly keeps this separate. The common implementation is selected before knowing the true law; a world-dependent fitted implementation is not substituted.

### 1.5 Minor domain precision requested

When a restricted prefix domain is used, policies and simulator kernels must still be defined on any histories the simulator can generate, or simulator support in that domain must be proved. Arbitrary zero-true-probability rows do not specify the simulator's own policy. A full syntactic history-tree extension solves this without changing true-law guarantees. The author was notified.

## 2. Positive implementation audit

The finite deterministic-response-table mixture criterion is exact for an unrestricted context-independent shared random source, with optional independent private randomness. The converse determinization proof is valid, as is its warning that moving private randomness into the shared seed can increase the seed alphabet. Thus deterministic-strategy support cardinality is not interchangeable with bounded common-source cardinality when private randomness is separately available.

The Caratheodory bound uses the affine dimension of the joint-context conditional table polytope and is sound. Source permissions, numerical sampling precision, initialization and table storage are not supplied for free.

For W={100,010,001}, every product support contained in W is a singleton; hence a static three-party independent-private-coin realization requires at least three shared-source values. The two grouped cuts admit binary-source implementations. Requested scope repair: this is a static/per-fixed-state kernel lower bound, not an unrestricted dynamic lower bound allowing additional persistent shared randomness or uncharged correlated initialization. The author was notified.

## 3. Example audit

The service mixture has strictly positive joint output rows. Exhaustive local-mask comparison correctly returns contexts (neighbor current readout, own previous readout, own action). The 110 atom weights sum to one and reproduce all joint tables. Independent marginal sampling can be wrong by TV=1/4. The one-bit local delay memory and one incoming current-readout bit are actual recursive operations with initialization/access requirements, not latent-state access.

The hidden two-mode example's log-odds update has contraction factor 4/5. Its rounding bound (5/2)d in log odds, (5/8)d in posterior probability, and .3d in one-step output TV are correct. The finite-state impossibility follows from infinitely many distinct predictive posteriors; the author strengthened it to a same-time family, removing any ambiguity from external clocks.

The example remains a population-table calibration. Full-history empirical verification without a memory promise has exponentially many rows. Its conditional-count confidence calculation is valid for independent complete episodes with a fixed generating regime, not arbitrary dependent sequential samples. The example does not establish practical finite-log discovery or an improved sample-complexity theorem.

## 4. Independent exact regressions

Three independent standard-library scripts pass:

- `tests/review_predictive_quantifiers.py`: 62 persistent-parameter conditional checks; fixed-world versus rectangularized disagreement 3/8 versus 3/4; persistent/fresh shared parity joint TV 7/8; 18 rare-history conditional failures; 19 finite-horizon nonextension controls.
- `tests/review_service_and_sources.py`: all 64 service contexts and 110 response atoms; unique minimal masks 22 and 41; eight passing masks per port; maximum independent-product discrepancy 1/4; three allowed W product-support rectangles; 200 contraction checks and 40 distinct exact posterior iterates.
- `tests/review_weighted_predictive_bound.py`: H=2, 81 recursive predictor tables, 32 deterministic full-history controllers; 13,689 exact rational bound/equivalence checks; 7,776 confidence-law convexity checks; 729 randomized-policy extremality checks. Evidence worlds are held fixed through complete episodes and mixtures generate genuinely history-dependent conditionals.

These regression checks support the written proofs but are not a formal general proof.

## 5. Assessment

No mathematical blocker found in Theorems 1–3 as scoped. The substantive technical distinction from the preceding risk-only observer milestone is a reusable positive recursive predictor with a controller-uniform joint trajectory guarantee, and a weighted residual that makes fixed-program synthesis linear while retaining approximate completeness.

Do not inflate this into efficient unknown-architecture learning, unrestricted infinite-time predictive realization, physical safety certification, or completion of the original categorical reconstruction contract. The nearest mathematical ingredients are standard. The current examples test the new obligations but do not yet demonstrate that the exhaustive discovery method scales or learns a useful nontrivial architecture from finite partial logs.

## 6. Subsequent extensions reviewed (15:26 UTC)

Sections 10 and 11 of the main theorem were added after the first review.

**Persistent family extension:** accepted as stated. The change-of-policy operator is linear on complete exploration laws, so one fixed alpha mixture of confidence vertices maps to the same fixed alpha mixture under every controller. Drawing the simulator branch only at initialization gives exactly the analogous mixture of simulator laws. Convexity of TV therefore proves both directions of the claimed policy-uniform Hausdorff approximation. The statement correctly does not identify the unknown physical world or grant runtime access to a simulator branch. The likelihood recursion requires joint response probabilities; its extra coordination and numerical-memory costs are explicitly charged. Without those resources, executable local prediction for the entire mixture family remains open, even though every branch has a local implementation.

**Evidence-dual LP:** accepted. Independent sign choices represent each weighted absolute residual exactly. For each fixed policy/sign choice, optimization over the same full confidence polytope has the displayed ordinary LP dual. Its upper/lower interval multiplier signs and the additive initial-law term are correct. A common mu,nu across every dual certificate is essential and is imposed. The coefficient vector d is technically affine in mu (rather than homogeneous linear), which has no effect on LP validity. Avoiding vertex enumeration is an alternative finite certificate, not an efficiency claim: sign patterns and policy trees can still be enormous.

## 7. Superseding finite-evidence review (15:41 UTC)

The preceding population-only assessment describes the earlier example version. A subsequent finite-evidence calculation is now reviewed: `examples/check_weighted_episode_discovery.py`, its saved histogram and JSON, and `examples/Finite_Evidence_Weighted_Discovery.md`. This supersedes the population-only limitation for this bounded synthetic instance; it does not establish efficient or general architecture discovery.

The run draws a compressed multinomial histogram representing 10,240,000 independent synthetic episodes, covering 1,088 full-history/action rows at H=2. Mask selection and rounded response tables are computed from those counts. The resulting two supplied ports use discovered scopes 22 and 41, corresponding to a neighbor's current readout, their own previous readout and their own action. The full-history validation does not infer or assume a second-order Markov law for the actual evidence-compatible environment.

### Statistical repair and verified scope

The first draft reported a sum of exponential tails evaluated at the observed random row counts as an unconditional coverage bound. That inference was not justified: conditioning on each row's own count does not license conditioning on all overlapping row counts simultaneously. This was corrected before acceptance.

The final version fixes exponent thresholds 13 for each four-outcome conditional row and 16 for the sixteen-outcome initial row. Integer-square-root rounding establishes exactly that 2*n*r_n^2 is at least the appropriate threshold unless the radius is one, in which case the failure event is empty. Conditioning on a fixed row's own visit count, then unconditioning and using a union bound, gives the deterministic failure bound

    14*1088*exp(-13) + 65534*exp(-16).

Exact rational Taylor sums through degree 100 lower-bound both exponentials, giving a conservative unconditional bound 0.0418042176672 < 0.05. This bound does not depend on the observed counts. Independent episodes, exogenous acquisition and policy-invariant response remain substantive assumptions; the simulation supplies them, ordinary physical logs need not.

### Weighted DP and useful rejection

The TV-ball water-filling operation exactly maximizes a linear expectation over the row ball. The backwards recursion maximizes the expected fixed error ENVELOPE gamma over independent full-history row balls and all admitted adaptive actions. This is an upper bound on J, not an exact optimization of J's nonlinear row-dependent residual. Independent row choice is legitimate here because it is the expressly defined evidence class; adding shared-parameter constraints would turn the same DP into an outer relaxation.

The initial discrepancy is bounded separately and then added to the worst initial-distribution expectation. These separately maximized quantities need not be jointly attained, but their sum remains a valid upper bound. The final result is

    J <= 0.0436124603725 <= 43613/1000000 < 1/20,

and therefore the same upper bound holds for complete-record TV. The uniform worst-prefix certificate is about 0.199983508647 and fails the same threshold.

The nominal positive predictor lies inside the confidence family. Pairing equal-mass initial histories yields lower J at least 1/10 for either specified omitted distinction. This is valid under the explicitly restricted local access contract, including no other action or message encoding the missing input as a free side channel. It is not a universal lower bound against relocated storage or other architectures, and not a claimed 1/10 lower bound on complete-record TV.

### Independent numerical and arithmetic check

`tests/review_weighted_episode_lp.py` reads the saved histogram directly and does NOT import the author's proposal, water-filling or DP functions. It independently recovers the masks and rounded local probabilities, verifies all 1,088 exact radii and nominal-feasibility inequalities, and evaluates 65 generic SciPy linear programs using an L1 epigraph rather than water filling. The recomputed bound is 0.04361246037245434, agreeing with the author's exact rational result within 1e-10. It also exactly reproduces the rational fixed confidence bound. PASS.

This additional check uses numerical LP optimization, not exact LP certificates; the author's main DP arithmetic is rational. The data remain synthetic, the horizon is two, every history is covered, and 10.24 million episodes is substantial even for this small case. No physical mechanism partition has been identified.

## 8. Main section 12 review

The predictor-occupation corollary and its separate J bound are sound. Extending a fixed true law by the candidate K at zero-probability prefixes is legitimate under exploration coverage, and the extension is fixed independently of controller choice. The reverse-prefix hybrid therefore weights errors by candidate occupancy. The bounded-function oscillation argument gives the displayed J correction with M_t and b_s, without conflating path-TV and J. This remains verification rather than convex synthesis because candidate occupancy depends on K.

Reviewed main source frozen by its author with SHA256:
`080a832d541e7075ce7e633e343695e00851676bc0b05ca75205a1a57cf6450a`.

## 9. Bounded fair-bit driver review (15:45 UTC)

The optional twenty-fair-bit source conversion is correct. For R=floor(200*U/2^20), exactly 176 driver values have 5,243 preimages and 24 have 5,242. The exact TV distance to uniform200 is 33/1638400. Deterministic local threshold processing cannot increase that distance. Since J is weighted by the unchanged true-process histories, replacing each candidate response row by one within delta_source changes J by at most H*delta_source, irrespective of controller adaptation. Initial sampling is unchanged.

`tests/review_bounded_source.py` independently enumerates all 1,048,576 fair-bit words and checks all 121 decile-threshold pairs (including contexts beyond the demonstrated subset). PASS. The exact H=2 bound becomes 0.0436527435756, outward rounded to 43653/1000000 < 0.05.

This supplies bounded random-bit consumption, conditional on a genuine independent fair-bit source and bounded arithmetic/delivery capability. The twenty-bit source input register, driver identifier, threshold delivery, observer memory and observation messages remain distinct costs. A numerical probability forecaster need not execute this stochastic sampler at all.

## 10. Final scope and report pass (15:47 UTC)

The final Section 7 clarification correctly separates finite discrete program/memory/wiring/support budgets from the encoding cost of LP-selected probabilities. A hard rational probability-bit budget is not imposed by the plain continuous LP; finite rational enumeration or an exact discrete restriction is needed for that stronger contract. Reviewed replacement main-source SHA256:
`0238ce12da776ee87110da734ceac2c766def7e8928c7da6da78c13477d542f6`.

The report draft was read end-to-end. No material mathematical or scope blocker was found. It correctly distinguishes the example's data-driven heuristic proposal plus sound verification from execution of the general exhaustive synthesis LP; lower J from lower path TV; ideal/numerical prediction from source implementation; and predictive scopes around supplied ports from physical partition identification. The requested final addition is the independently checked twenty-fair-bit driver, whose bound is 0.043653 rather than the ideal-source/numerical predictor's 0.043613. These numerical variants should remain separate.
