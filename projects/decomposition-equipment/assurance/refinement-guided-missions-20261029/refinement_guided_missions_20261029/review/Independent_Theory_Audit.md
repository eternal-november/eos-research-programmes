# Independent theory audit — restricted delayed-resource target

29 October 2026. Reviewed `theory/Refinement_Guided_Target.md`, `TARGET_GATE.md`, and `design/Substantive_Mission_Family_Proposal.md`. This audit does not edit those sources, run a mission benchmark, or assert literature-wide novelty.

## Decision

**Pass the restricted theoretical target, with explicit implementation contracts below. Do not interpret this as clearance for a main outcome experiment or a demonstrated cost advantage.** The exact nonnegative sparse-grid FIR subclass admits sound refinement, a genuine temporal certificate separation, safe singleton identification, exact fixed-schedule robust checking, and at most n new-column resolutions. The source already appropriately limits its main claim to safe finite diagnosis with conditional completion.

Independent checks passed: all 8 orientations and 6 two-batch cuts of a four-job path; 22,272 exact top-k comparisons over 73 sparse rational rows; bounded-error singleton recovery at noise endpoints; strict-gap boundary ambiguity; post-service delayed violation. The code imports only Python standard-library modules and does not import any author checker or learner. These are proof regressions, not empirical support for a benchmark advantage.

## 1. Refinement: correct quantifiers and cost meaning

Fix policy space Π, observations, admissible disturbances, actual starting history/state, task, resource ledger and stopping rule. Let W(K) contain policies whose executions satisfy safety and completion for every fixed G in K and every allowed disturbance history. Then K_f ⊆ K_c implies W(K_c) ⊆ W(K_f), simply by restriction of the universal G quantifier. A policy remains the same function of permitted histories; it is not allowed to inspect G. Adaptive observation branches are already inside its execution semantics.

For randomized policies the statement holds either for every seed (sure guarantee) or for probability-one success separately in each fixed world, provided the same notion is used on both sides. For a fixed policy, supremum cost over the smaller uncertainty class cannot increase; infimizing over the expanded feasible policy set preserves this inequality. This compares the same present state and ledger, **not** free learning: a physical probe can improve knowledge while consuming time and shrinking residual completion opportunities. Consequently global end-to-end cost need not improve after acquisition.

Different factorizations of an identical coherent model set preserve W exactly. This law is a general monotonicity fact, not novelty and not a performance separation from a same-information dense model.

## 2. Strictness seed: valid, including adaptation and randomization

Assume q ≥ 1; exactly 2q indivisible unit-service jobs; actions only in slots 0 and 1 for commanded service; at most q jobs per slot; no pre-slot-0 information beyond the declared coarse summary; zero pending input; one-slot edge tails checked in slot 2. Fix the directed convention that an edge points from its current endpoint to its delayed endpoint. Every orientation of a path is acyclic. A topological prefix of q vertices is a safe first batch: no delayed endpoint appears before its current predecessor across the cut. Within a batch the contributions occur at distinct times; across batches the current contribution appears at 0 and delayed contribution at 2. This proves the fine schedule including its tail.

For a deterministic policy, completion forces an initial q-element batch B and its complement in slot 1. Connectivity gives an edge across B. Fix, before execution, an allowed world where the B endpoint is delayed and the other endpoint is current. In that world the remaining unit pulse collides at slot 1. Runtime observations can tell the policy to abort but cannot restore completion by the deadline. Thus every policy has some fixed compatible defeating world. No world-switching along an execution is needed.

The source's conclusion about randomization is right, but “a spoiling world for every realized seed” alone would not prove it for an arbitrary infinite world set. Here there is a short rigorous repair. The initial q-element batch ranges over a finite set of size M = binomial(2q,q). Some batch B has probability p ≥ 1/M (or a non-q batch already causes failure). Fix a world spoiling B. In this single world the policy fails with probability at least p, whatever later observations or random choices occur. Therefore probability-one robust completion is impossible. No adversary sees the random seed, and one world need not spoil every policy. The rational regression checks the finite combinatorial premise; this paragraph supplies the all-policy argument.

The result needs the indivisible job/action restriction. Fractional service, extra diagnostic substeps, an orientation-revealing prehistory, or a deadline that permits additional commands would require a new argument. Fine/coarse commissioning costs are not compared by this post-commissioning witness. It remains a sanity seed, not the substantive motivating family.

## 3. Safe singleton acquisition: separate three quantities

Use distinct notation before implementation:

- x_i(t) = FIR_G[u]_i(t) + d_i(t): physical constrained load;
- z_i(t) = x_i(t) + ν_i(t): sensor readout;
- d: actual omitted dynamics, baseline uncertainty or physical disturbance; ν: measurement error.

If the acquisition model has |d+ν| ≤ η_total after appropriate known-baseline subtraction, then z/ε lies within η_total/ε of the grid coefficient. The strict condition εΔ > 2η_total ensures unique nearest-grid recovery, including zero coefficients. Sensor error alone does not increase true physical load. Conversely a physical disturbance must be included in safety even if sensing were perfect. A sufficient singleton safety bound is εg_max + d_upper ≤ c_i for each row, not merely a bound using the sensor error. If d is absent in the exact synthetic model, state d=0. The source mixes these meanings in its initial y/e notation but later distinguishes physical residual allowance; the implementation must remove that ambiguity.

A single isolated pulse at j produces at lag ℓ exactly εG[i,j,ℓ]. Even if a row has many taps on that input, they arrive at different timestamps, so the peak bound is εg_max, not εs g_max. Read all lags 0 through L and all declared outputs. Exact grid identification requires an **admissible executable amplitude** ε satisfying the gap, power, capacity and command-alphabet constraints, not merely a real number below an upper bound. A discrete alphabet may make safe identification unavailable. The gap is strict: at εΔ = 2η_total, adjacent coefficients can produce an identical observation with opposite endpoint errors; an independent test verifies this ambiguity.

A flush is an action sequence, not a state assignment. Its entire trajectory must already be certified safe for the pending actual history. Nonnegative delayed loads can rise while every current command is zero; a safe current reading alone does not justify a safe flush. After a safe finite-FIR flush, samples from distinct probes are isolated. An infinite physical tail never becomes exactly zero after L ticks: its certified residual must remain in both safety and identification budgets. Without that bound the theorem applies only to the synthetic FIR class. Every subsequent mission must also check its complete terminal tail (or a valid infinite-tail stopping certificate).

## 4. Exact top-k envelope: sound for its stated information class

For each row, fix known columns and their exact values. Remaining sparsity k is s minus the known positive-tap count. Each unmeasured pair (j,ℓ) has a nonnegative weight u_j(t−ℓ). With independent row-wise constraints, maximizing a nonnegative linear expression chooses up to k largest weights and sets their coefficients to g_max. All other unknown taps can be zero. This constructs an admissible fixed row achieving the bound at the selected time. Completing other rows arbitrarily within their constraints yields a persistent full operator.

Universal fixed-schedule safety is ∀G ∀t; its quantifiers commute. Checking each time's exact maximum is therefore valid even though different maximizers occur at different times. A failing time needs only one fixed operator witness. This reasoning does not validate a simulation that changes operators during an actual trace, or optimize a general observation-dependent policy with a fixed-schedule formula.

If the retained evidence includes runtime joint measurements, cross-row relations, row-sum bounds or additional physics, known columns need not characterize the exact knowledge set. The top-k formula is then a conservative upper bound after deliberate overapproximation, not necessarily an attained compatible-world witness. Preserve that evidence and use exact constrained optimization when claiming a compatible counterexample or exactness. Likewise retain all supplied sparsity/grid promises for the dense baseline.

## 5. Finite progress is not planning tractability or guaranteed success

Unknown-zero coefficients give an optimistic capacity relaxation only because coefficients and commands are nonnegative and the task's feasibility requirements do not require a positive unknown resource response. Known loads, physical residual allowances, actual pending history, deadline and other shared limits must be included identically in both candidate and robust checks. Under these premises, exact optimistic infeasibility rules out a completing open-loop schedule in the declared grammar for every remaining operator. It does not establish global impossibility outside that grammar; a timeout establishes neither.

If a candidate satisfies the optimistic checks but fails the robust envelope, at least one strictly positive unknown tap contribution exists. Resolving its unmeasured column decreases the integer potential n−|J| by one. Thus at most n−|J_initial| such successful probe refinements occur; at most one final scheduling/check attempt follows. This proves finite *column progress*, conditional on each probe's safe executable precondition and sufficient residual resources. It supplies no polynomial bound on complete finite scheduling search, witness selection or evidence-conditioned optimization. If a probe becomes unavailable, the procedure must abstain or use another separately verified action, not claim completion.

The ledger must charge initial/transition flushes, (L+1) ticks per isolated probe, all readings, sensing/communication precision, planning/checking time when it consumes mission time, and final stopping tails. Observations and low-amplitude actions that complete real service must receive the same credit for every method. Distinct probe count alone is not a performance metric.

## 6. Reuse and next release gate

Reuse requires the same persistent operator and verified input regime, sensor/output meaning, grid and lag assumptions. Carry actual history across task boundaries; either prove composition with its tail or pay a safe flush. A previous certificate is reusable only under its stated resource/history assumptions, not merely because the task name resembles an old task. Unseen mission combinations can reuse identified coefficients, while their schedules still need checking.

Direct scaled rehearsal must include physical residuals and sensor uncertainty: dividing a low-amplitude reading by α amplifies additive observation error by 1/α, and arbitrary physical disturbances do not scale with the command. This does not remove rehearsal as a mandatory baseline. Dense/cached methods may infer the same sparse operator from the same records and tie; the named non-reusing rehearsal amortization calculation is not a lower bound on all such methods.

Before main outcomes: freeze a genuinely overlapping multi-stage/multi-lag task family and finite scheduling grammar; specify amplitude alphabet, observation contract, physical/sensor envelopes, safe initial history and paid transition rules; preserve evidence and matched comparator permissions; obtain the independent nontriviality/baseline review. No claim of material cost separation follows from this audit alone.

## Reproducibility and status

Run `python review/independent_exact_checks.py` from the target directory. Output is recorded in `review/Independent_Exact_Checks.json`. All checks passed on 29 October 2026; no source was modified. No permission block, full experiment, hardware access, novel-method claim or external publication occurred. Complete for the requested restricted theoretical audit; the main experimental gate remains distinct.
