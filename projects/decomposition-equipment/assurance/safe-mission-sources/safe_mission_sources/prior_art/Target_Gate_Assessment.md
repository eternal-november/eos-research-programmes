# Independent target gate assessment

29 October 2026. Initial assessment of `example/BENCHMARK_DESIGN.md`, before implementation outcomes.

## Current decision: strengthen before treating as main hard target

The initial deterministic guard design is a useful baseline fixture. It explicitly fixes the preceding stopping example's supplied history, uncharged resets, lack of positive travel, and missing mission objective. It also proposes serious oracle and centralized references, exposes synthesis cost, and distinguishes physical premises from discovery.

However, it is not yet a sufficiently strong main target for the user's request to prefer the hard problem. Each readout is an independent unknown static Boolean function of supplied command-run counter features. Observations constrain each candidate set separately; product closure is a property supplied by the model class. Learning sparse guard dependencies in expanded fluents, then invoking a planner, is closely related to safe action-model learning. Nonmonotone truth tables, shared command ports and deadlines make planning nontrivial, but do not alone establish discovery of interacting environmental components or preservation of coupled epistemic uncertainty.

## Recommended strengthening

Retain the fixture, then add an interacting family in which either:

- endogenous readout/state variables have unknown local cross-dependencies and are only partially observed between bays; or
- permitted diagnostics constrain combinations of persistent mechanisms, so the residual uncertainty is genuinely nonproduct and preserving those constraints changes mission admissibility.

The interface vocabulary may be supplied, but not the actual factor graph, mechanism tables, dependency scopes or useful observer. An explicit factor/variable-elimination representation can be used if its conditioned separator width is checked and its cost recorded. Do not infer inference tractability merely from sparse transition scopes. Generic search can propose a controller/witness, with independent compact checking, provided the expensive proposal cost is visible.

The strengthened example must demonstrate that the coupling is operationally used, rather than present in a diagnostic subplot that the final controller ignores. Compare sound coherent inference with a labeled conservative rectangular relaxation. If they make identical decisions, do not claim demonstrated benefit from preserving coupling.

## Safe indistinguishability wording

Model identification is not necessary for safe completion. Different surviving models may admit the same safe successful strategy. The obstruction must concern lack of any common completing strategy under observational equivalence, not merely failure to identify the true mechanism.

A precise finite example may exhibit two models with identical laws for every permitted safe probe before an irreversible decision, but incompatible goal-enabling actions. A common controller then cannot select model-specific actions from that shared history. The conclusion depends on the required safety/progress quantifiers and permitted randomization. If a common conservative route finishes the task, or further safe information is obtainable, the obstruction does not apply.

## Revised coupling proposal: conditional pass for integration tests

The benchmark worker's revised proposal uses joint sum diagnostics on pairs of unknown guards. Coordinate observations first constrain local tables and scopes; a joint report then relates the still-possible persistent mechanisms. The sensor pairing is declared instrumentation, not a discovered component graph. This is genuinely nonproduct evidence, and a sound rectangular projection can lose goal-relevant information. It addresses the initial product-closure criticism without a whole-environment candidate catalogue.

The specifically proposed true family nevertheless has a narrow residual: three Boolean table rows are identified, leaving an OR-versus-XOR choice at row 11. Pair-sum reports equal to one impose a binary parity relation along a sensor tree; one individual observation resolves the connected component. This is elementary constraint propagation. It is useful for auditing coherence and evidence transfer, but must not be presented by itself as a novel inference algorithm or a general hard-discovery solution.

Conditional permission from this independent audit is to use it as an integration benchmark under a broader theorem. To strengthen the motivating family, retain multiple unresolved table rows or scopes and use context-dependent diagnostics that constrain different candidate signatures. Mission certification should use these relations, not merely recover a common hidden bit. Keep the supplied sensor topology, learned response scopes, and inferred epistemic relations distinct.

The independent centralized solver should match attainable capability on small instances. The rectangular ablation intentionally discards information and must be named as such. Completing more tasks than that ablation establishes the operational importance of keeping correlations, not superiority over an information-equivalent optimal controller.

## Independent theorem review, 21:01 UTC

Read `theory/Safe_Discovery_Mission_Theorem.md` in full and reran `check_relational_discovery.py`. The run passed 450 forest instances against 260,931 complete assignments, 334,368 observer-update cases, inconsistent-component handling, persistent successor partitioning, nonproduct counterexamples and cycle rejection.

No mathematical blocker was found in the current forest signature-message proof, deterministic adaptive consistency update, observer truncation, finite-rank mission certificate, module frame conditions or safe-indistinguishability argument. The latter explicitly permits success without identifying the model when a common safe completing policy exists. The theorem credits standard CSP/semijoin, game and rank mechanisms and exposes global synthesis and query-induced width costs. An editorial correction was requested because Section 5's displayed knowledge-state tuple initially omitted the retained relational factors despite using them later.

The theorem is broader than the parity-chain example: repeated contextual observations operate on arbitrary remaining domains of local response functions, with exact persistent compatibility constraints. That is a meaningful conditional integration construction. It is not a theorem that efficient safe acquisition is always possible, nor that the useful model class or diagnostic forest can always be found. The run-counter grammar and permitted observation form are supplied; these are legitimate assumptions but limit the discovery claim. A generic controller search remains potentially exponential.

**Gate decision:** proceed with implementation as a bounded discovery-to-safe-mission integration milestone, provided the final claims retain these limits and the example includes richer residual ambiguity or is explicitly identified as the narrow parity special case. This does not grant a mathematical-novelty, general-decomposition or hardware-assurance claim. If the concrete results establish only the narrow special case, say so rather than converting this conditional gate into evidence of broader empirical success.

## Status

The benchmark and theory workers and parent have been informed. The current theorem/design is conditionally accepted for the bounded milestone, with empirical realization and final-claim alignment still to be checked. This is not an invalidation of prior results or a claim that safe action-model learning subsumes every possible extension.
