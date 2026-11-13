# Prospective refinement guided mission gate

29 October 2026. Independent target-selection analysis. No new mission experiment has been run.

## What the prior experiment taught us

The preceding 48-root mission comparison was nondiscriminating. Both methods won the same 12 roots at the same minimum cost. Inspection of saved policies found identical winning trees, all using the all-off command and minimum preparation. This is a benchmark design failure for the proposed capability comparison, not evidence that relational distinctions lack mission value. The rectangular baseline also inherited already-pruned local domains, so it isolated retention of remaining relations rather than the whole benefit of discovery.

The repair is prospective: before constructing a benchmark, prove that its objective depends on a distinction or a measured resource that the competing representations treat differently. A strictness example need not be a new theorem, but it must be valid under the actual controller and resource interface.

## Nonnegotiable comparison semantics

For equal controller interfaces and resources, a coherent possible-world set K refines a sound overapproximation C when K is a subset of C. Every policy robustly winning for C remains winning for K; minimax cost cannot increase. This does not force strictness.

A factorization change representing the same coherent behavior need not change capabilities. Its benefit can be discovery, storage, communication, synthesis or checking cost. Do not use more completed missions as the only success criterion for a behavior-preserving decomposition.

An arbitrary controller given the original raw history may reconstruct information discarded by a named abstraction. Therefore a lower bound on a coarse representation is not a lower bound on all same-data controllers. State whether the result concerns robust certification under a particular model, a physically justified information interface, or an explicitly bounded computational representation. All private memory, retained histories, time, resource observations and policy parameters belong to that accounting.

## Gate before implementation

1. Give the refinement witness and prove preservation under the actual observation and action interface.
2. Give either a strict robust winning/cost witness or a representation-cost separation. Name the coarse obstruction, and show that it is impossible in the finer coherent class.
3. Show that a strong comparator cannot bypass the obstruction through another permitted probe, route, schedule, private memory or available resource.
4. Make the needed fine information safely attainable from a justified initial state. Do not supply the actual decomposition, hidden mode, diagnostic answer or favorable history.
5. Prove that the discovered object can be reused for a family of mission combinations, not only the separating fixture.
6. Keep synthesis, inference and experiment costs visible. A compact certificate does not imply cheap synthesis.
7. Require a substantive growing interacting family. A tree of OR/XOR gates, one hidden bit, independent doors, or a static conflict graph is a diagnostic fixture rather than the motivating hard result.
8. Freeze task distributions, action interfaces, budgets and comparisons before outcomes. Preserve failed comparisons without searching seeds until a win appears.

## Nearest prior art

### Counterexample guided refinement already answers the structural question

[Counterexample-guided Planning](https://goto.ucsd.edu/~rjhala/papers/counterexample-guided_planning.html), Chatterjee, Henzinger, Jhala and Majumdar, UAI 2005, adapts abstraction refinement to adversarial stochastic planning. An abstract spoiling strategy may be real or spurious, and refining a coarse model can restore a winning strategy. Thus using a mission obstruction to guide refinement is established, not itself a new contribution.

[Abstraction Refinement for Games with Incomplete Information](https://finkbeiner.groups.cispa.de/publications/2008-abstraction-refinement-for-games-with-incomplete-information/), Dimitrova and Finkbeiner, FSTTCS 2008, incorporates players' knowledge and move approximations into an abstract game; strategy-tree formulas check concretizability and interpolation supplies refinement predicates. It explicitly addresses the danger of strategies using information unavailable to the controller.

[Compositional abstraction refinement for control synthesis](https://arxiv.org/abs/1712.06013), Meyer and Dimarogonas, treats supplied nonlinear dynamics with reachable-set overapproximations and location-sequence objectives. Compositional control refinement is therefore also a substantive comparator.

### Learning a property-relevant model without first learning the whole plant is established

[Efficient Black-Box Checking with Specification-Guided Abstraction](https://doi.org/10.1145/3762659), Matsumoto, Watanabe, Suenaga and Waga, TECS 2025, directly learns a specification-guided abstract Mealy machine instead of first reconstructing complete behavior. Its purpose is black-box testing/model checking, not a blanket guarantee that physical acquisition itself is safe. The distinction must be inspected rather than assumed.

The prior audit also covers safe action-model learning, partial-observation SAM, Conditional-SAM, SAM+, unknown-factor MDP learning, safe exploration and compositional shields. Merely adding sparse scopes or an active query policy does not remove these comparators.

### Thermal and delayed system identification is not an empty application category

[Safe Exploration for Identifying Linear Systems via Robust Optimization](https://arxiv.org/abs/1711.11165), Lu and colleagues, 2017, studies unknown noisy linear systems under trajectory constraints from a known nominal safe action, motivated by data-center cooling. A thermal network plus safe identification is therefore insufficient by itself.

[Sparse identification of nonlinear dynamics for model predictive control in the low-data limit](https://pmc.ncbi.nlm.nih.gov/articles/PMC6283900/), Kaiser, Kutz and Brunton, connects sparse learned controlled dynamics to MPC. It does not supply all our desired guarantees, but blocks novelty claims based simply on sparse dynamics plus useful control.

[Adaptive learning-based model predictive control for uncertain interconnected systems A set membership identification approach](https://www.research-collection.ethz.ch/entities/publication/2a8c50f0-4a4a-4f7d-8b79-6645d6419234) is a close uncertain-coupling comparator. The supplied versus discovered subsystem structure must be compared explicitly before claiming a decomposition contribution.

Access qualification: the Black-Box Checking publisher page and ETH publication page returned HTTP 403 on direct open in this pass. Their bibliographic identity and abstract-level descriptions were available in indexed results and author publication pages; full-paper assumptions have not been audited here. The CEGAR, compositional refinement and safe linear identification primary pages were directly accessible. Do not turn these comparator pointers into claims of full subsumption.

## Strong candidate direction

The most promising additional burden is evidence-constrained refinement. A coarse mission spoiling strategy identifies an obstruction, but the concrete plant is unknown: the learner cannot ask an omniscient concrete-model oracle whether the obstruction is spurious. It must choose safely reachable, resource-charged experiments whose possible outcomes either support an executable scope/memory/interface refinement or leave a genuine information obstruction.

A worthwhile theorem would state finite conditional progress or completeness under an explicit safe-distinguishability/access premise, preserve one coherent persistent environment through refinements, and avoid first enumerating all whole-system models. A dynamic thermal or shared-capacity system could instantiate it, but must contain substantive history and coupling interactions rather than a renamed bit puzzle.

This is a candidate, not a proven result or literature-wide novelty claim. A generic exhaustive search over all policies and models with a stopping rank would not meet the practical discovery target.

## Current decision

No implementation target has yet passed. Delayed thermal/resource candidates are plausible and stronger than independent logical guards, but require a prospective strictness proof, safe acquisition algorithm and serious matched-memory/dense-model comparator. Keep selection open until those are explicit.

## Concrete proposal review, 21:45 UTC

Read `theory/Refinement_Guided_Target.md` and `design/Substantive_Mission_Family_Proposal.md`.

**Verdict:** conditional approval of the delayed-resource/FIR direction for further theorem design; **not yet approval for main experiments**. This is not a novelty veto. Known safe identification, refinement and scheduling mechanisms may support a worthwhile distinctive discovery/reuse integration if its actual mission relevance and costs are demonstrated.

The two-slot path witness appears correct under the declared fixed unit-service pulse grammar, zero pending input, and no spare predeadline diagnostic time. A balanced first-slot batch creates a crossing edge; a fixed orientation compatible with the coarse summary makes its delayed first-slot contribution collide with the required second-slot contribution. Runtime observations cannot repair the deadline. The fine ordering avoids every collision and checks the terminal tail. The proof is an all-policy robust certificate separation, not just failure of a chosen planner. It does not establish an unrestricted same-raw-data information gap.

The isolated coded two-tap acquisition proof also appears correct under nonzero distinct port codes, adequate coefficient/noise resolution, a justified flushed start, all-resource readout, and explicit shared-power/capacity bounds. Its logarithmic pulse count is standard coded identification in this supplied two-tap class. Sensor volume, flush time and amplitude feasibility remain part of cost. This does not yet prove a safe multi-tap support learner or an advantageous evidence acquisition bound against a dense learner permitted to use the same structural promise.

Two accounting additions are important:

- A strictness comparison may legitimately start from different knowledge at the same physical state. An end-to-end mission comparison must additionally charge commissioning, its pending tails and any synchronization needed to attain that physical state. Do not compare a fully commissioned fine controller with an uncommissioned coarse controller under only the execution deadline.
- Low-amplitude probes may do useful work if the service semantics permit fractional work. Excluding that possibility is valid for genuinely atomic pulses/jobs, not merely as a favorable benchmark restriction. General sustained-service missions should account for probe-generated progress consistently.

The remaining release blockers are exactly those acknowledged in the proposal: a growing genuinely overlapping multi-tap/multistage family, a safe finite acquisition/refinement argument for that family, and an actual cumulative cost witness. Direct scaled rehearsal and information-equivalent dense inference with caching are indispensable comparators. Dense may exploit zeros and discover the same factorization; this must count as a legitimate competing method, not a violation of baseline rules. The path proof alone must not become the headline result.

## Singleton-column proposal: analytical conditions

The fallback to isolated input-column probes is mathematically cleaner than requiring a sparse coded learner. For a flushed exact FIR system with coefficients in a known finite grid of minimum spacing Delta, inject `u_j(0)=epsilon`, all other commands zero, and read each output for lags 0 through L. If total measurement uncertainty per readout is eta, `epsilon*Delta > 2*eta` makes grid decoding unique. Physical uncertainty and sensor uncertainty should be distinguished; both enter eta when inferring the operator, but only actual output uncertainty belongs in the capacity bound. With known coefficient upper bounds B, require `epsilon*B[i,j,l] + physical_margin[i,l] <= c_i` for every output/lag, plus the shared-power constraint and safe startup/flush envelope. Nonnegative isolated impulse responses make this a straightforward robust safety proof. A nonzero unknown baseline must be known, measured with appropriate extra error, or retained as uncertainty.

One probe identifies all output/lag coefficients in a previously unresolved input column, including certified zeros. At most n such new-column probes identify the full operator. This is not a sparsity-dependent evidence improvement and not a bound of n on arbitrary planner/refinement iterations. Each probe costs its complete L+1 readout window plus any required physical overhead; shared sensing records are charged once and available to dense comparators.

A failed candidate trace does not always contain a useful unresolved column: it may fail even under already known coefficients, or reflect purely combinatorial scheduling infeasibility. The procedure must then replan, refine representation without measurements, or declare appropriate failure. Finite termination of the full loop requires an independently specified finite exact feasibility procedure, finite monotone representation refinement, or an explicit fallback to full-column identification and exact search. The n-probe argument alone does not establish that termination.

The guarantee is safe acquisition followed by a sound completion certificate or safe abstention. Safe acquisition does not imply that the remaining mission is feasible: probes consume time, energy and potentially useful service. A stronger completion theorem needs a total budget that includes worst-case acquisition, all tails and the subsequent feasible plan. If commissioning is separated from mission execution, show that separation explicitly in the evaluated cost ledger rather than hiding it.

## Final theoretical gate, 21:52 UTC

**PASS for implementation and prospective main-family evaluation**, based on the appended multi-tap acquisition proposition, finite task-directed acquisition guarantee, and substantive multistage workload definition in `theory/Refinement_Guided_Target.md`.

The finite-grid, bounded-noise disjunct-code reconstruction proof is sound. At every output/lag, disjunctness supplies a clean exclusion test for each absent input and an isolating test for every present input. The strict gap `epsilon Delta > 2 eta` ensures threshold support recovery and unique grid rounding. Isolated complete-tail pulses and the stated a priori capacity/power bounds establish safe acquisition without knowing actual wiring. The singleton identity code is a fully valid fallback; its sharper peak bound is `epsilon*g_max`, rather than the safe but unnecessarily restrictive general `epsilon*s*g_max` bound. The full code is injective on the declared class; distinct retained operators with mission-relevant differing responses therefore have a separating measurement among as-yet unissued tests. Bounded noise cannot make different grid-separated test values jointly consistent with the same recorded sample. At most R distinct tests identify the operator. The proposal now correctly distinguishes this finite acquisition result from complexity, mission feasibility and total-loop termination.

The exact synthesizer, remaining-resource, safe reserve and safe abstention qualifications are appropriate. No universal cost win is asserted. The non-reusing rehearsal crossover is explicitly labeled a strategy comparison, not a lower bound against optimized inference/caching. This satisfies the balanced practical-contribution gate.

The main-family description is substantively adequate: overlapping multi-output multi-lag constraints, positive multistage work, release/deadline and shared-power restrictions, terminal-tail checks, and changing mission compositions. It is not yet a numerical preregistration. Before outcome runs, the implementation team should freeze the actual n/L/s values, support-overlap rule, coefficient/noise settings, stage counts/durations, workload-window/load regimes, seeds, solver limits, and all commissioning/execution budgets in a manifest. Include all generated outcomes, infeasibility and timeouts; do not filter for advantage. This is a normal pre-outcome freeze, not a demand for another conceptual redesign.

No implementation or outcome experiment was performed by this reviewer. Parent, lead designer and implementer were notified of the pass and remaining preregistration requirement.
