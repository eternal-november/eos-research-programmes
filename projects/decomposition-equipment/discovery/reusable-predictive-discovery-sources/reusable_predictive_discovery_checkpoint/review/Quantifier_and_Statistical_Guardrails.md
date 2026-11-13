# Independent review: predictive reuse guardrails

29 October 2026. Preliminary review, before the main theorem is written. These are scope tests and counterexamples, not new positive results or novelty claims.

## Plain-language abstract

A collection of locally accurate forecasts is not necessarily one coherent model of an environment. The same unknown environment must remain in force at every time and across every component. A finite set of observations also cannot certify arbitrary future prediction without a restriction on the processes being considered. The proposed theorem should preserve these restrictions explicitly rather than let the discovery algorithm switch models between predictions.

## 1. Same world, not pointwise conditional forecast sets

Let P_theta be an iid Bernoulli process, with theta either 1/4 or 3/4, fixed throughout an execution. Every finite history has positive probability under both worlds. At every history the set of admissible next-bit probabilities is exactly {1/4,3/4}. A predictor retaining only this set has forgotten which repeated selections belong to the same world.

In either original world, P(X1 != X2)=3/8. Taking the initial probability as 1/4 and then selecting 3/4 after X1=0 and 1/4 after X1=1 gives disagreement probability 3/4. Every selected conditional belongs to the correct local set, but the generated law is not an admissible original world.

Required repair: retain a globally indexed family of kernels or equivalent extension constraints; a product of local uncertainty sets is merely an outer approximation. Such an approximation can support conservative bounds but is not exact reconstruction and can destroy useful discoveries.

## 2. Marginal recursion is not joint recursion

Let B be one persistent fair bit, R_t fresh independent fair bits, and X_t=R_t, Y_t=R_t XOR B. Each marginal process is iid fair. Replacing B by fresh independent bits B_t leaves every entire single-sensor process law unchanged, but changes the joint law. At T steps the total variation distance between persistent and fresh joint laws is 1-2^{1-T}.

Thus two memoryless marginal predictors are not a joint predictive decomposition. A legal construction must retain the persistent shared distinction and account for its initialization, accessibility, storage, and any communication. A simulator may sample a hidden B; a real runtime observer cannot simply assume it knows B before observing appropriate joint information. This distinction between a generative witness and an executable predictive state must remain explicit.

## 3. Finite evidence cannot guarantee unrestricted infinite reuse

A process outputting H zeros and then one agrees through H steps with the always-zero process. More generally, suppose evidence constrains only laws through H and the admitted continuation class is otherwise all causal laws. For any fixed finite-state observer, extend a feasible positive prefix to more distinct same-length histories than its number of states. Two histories collide. Define their next-output kernels differently. This extension preserves the evidence but defeats predictive sufficiency of the observer.

The construction requires a nonempty evidence class and an observation alphabet admitting enough continuations; it is not a claim about a class with a declared finite-memory constraint. Its purpose is to identify the promise the positive theorem needs. Finite horizon, bounded memory/rank with realization conditions, or an explicit approximation/regularity assumption are legitimate. Finite data alone is not.

## 4. Conditional accuracy requires coverage

For epsilon>0, let P(0,0)=Q(0,0)=1-epsilon, P(1,0)=epsilon, and Q(1,1)=epsilon. Joint TV is epsilon, while conditional TV given the first output equals 1 is one. At zero-probability histories, the law does not determine a conditional at all.

A theorem transferring finite-horizon joint laws under covered policies can avoid claiming uniform history-conditional accuracy. A theorem claiming uniform conditional prediction needs explicit positive denominators and sensitivity bounds. An arbitrary zero-row completion may be harmless for laws under supported interventions, but not if a new policy can reach that row.

## 5. Controller quantifiers

Two worlds with next output f0(a)=0 and f1(a)=a agree under the controller always choosing action zero. They disagree under action one. Discovery based on one closed-loop law is not controlled-law discovery unless causal support and intervention assumptions justify it.

The installed encoder, communication schedule and update must be common over the declared controller family and unresolved worlds. World-specific predictive kernels can remain proof witnesses, but cannot become unobserved inputs to the installed program. Distinguish:

- one common executable observer with a family of predictions;
- one actual stochastic physical implementation with a world-indexed semantic witness;
- separately fitted observer programs chosen using the unknown world.

Only the first two can support reuse without further identification. Policy identification must not be leaked through a fitted initialization or a controller-specific history distribution.

## 6. Statistical selection

A confidence statement valid for one preselected observer is not automatically valid after searching many observers or controller policies. A simultaneous confidence event for a shared causal law family can transfer to every policy satisfying the support assumptions, without a fresh union bound over policies. But controller-specific importance weights, conditional normalization, fitted feature programs and adaptive measurements require the actual confidence construction to cover those choices. State this at the level of events/quantifiers, not only pointwise estimates.

## 7. Positive realization vocabulary

Nonnegative stochastic kernels may have zeros. Strict positivity is stronger and often excludes deterministic executable updates. A theorem should say which factors are nonnegative, which denominators must be positive, and whether positivity margins are assumed or inferred. A nonnegative factorization at a single time cut does not by itself establish simultaneous factorization, stochastic recursive closure, or a common shared-source realization across crossing cuts. Conversely, an arbitrary real-valued belief recursion is not finite-bit memory: count numerical precision and error if executability is claimed.

## Independent checks

`tests/review_predictive_quantifiers.py` uses exact fractions. PASS: 62 persistent-parameter conditional checks; disagreement 3/8 versus 3/4; four-step persistent/fresh joint TV 7/8; 18 rare-history examples; 19 finite-horizon nonextension examples. These validate the listed failure modes, not the main discovery theorem.
