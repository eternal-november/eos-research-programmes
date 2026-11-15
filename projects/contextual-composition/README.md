# Contextual Composition

A category-valued relative construction for independently specified context and content, with dependent protocols and comparison semantics.

Start with the [integrated treatment](synthesis/Integrated_Relative_Computation_Acceptance_Dossier.tex). Its O1–O7 claims are scoped by the [expanded contract](contracts/Expanded_Research_Contract_v0_1.tex), [boundary amendment](contracts/O6_Boundary_Amendment_2026_11_01.tex), and [portfolio freeze](contracts/O6_Portfolio_Freeze_2026_11_01.tex).

The [feedback and concurrency extension contract, v0.1.3](contracts/Feedback_and_Concurrency_Research_Contract_v0_1_3.tex) separates categorical-core obligations, semantic realizations and application evidence for general recursion, interfering concurrency and contextual refinement. Its obligations are research targets, not completed results. The [previous v0.1.2 contract](contracts/Feedback_and_Concurrency_Research_Contract_v0_1_2.tex) remains available.

## Reading guide: three levels

The programme distinguishes its categorical core from particular realizations and from applications. These are levels of abstraction, not rankings of mathematical value. A realization may have a substantial, reusable theory of its own and still be a relative example of contextual composition, just as robot transactions are.

### 1. Categorical core

Start with the integrated treatment linked above. Read its claims with their stated categorical hypotheses: independently specified context and content, their interaction, and the resulting relative construction and comparison maps.

- [Provisional interactad terminology](foundations/terminology/Interactad_Terminology_Note.tex): names for the presented context/content interaction package and its induced and framed forms, distinguished from realizations and applications.
- [Retained fibre effects and guarded prefixes](foundations/retained-fibre-effects/README.md): a Set-based construction parameterized by a commutative affine monad, with supplied conditional effects, native writer crossing and guarded prefix transport; semantic instances and exact presentation limits are stated separately.
- `foundations/`: finite contextads, reduction tests, structural examples, theory guide, and the common relative construction.
- `interaction/`: feasibility, the indexed receipt construction, and the independent interaction criterion.
- `framing/`: external framing and representation comparison.

These directories also contain structural examples and reduction tests; location alone does not make every result a theorem about arbitrary contextads or contentads.

### 2. Model realizations and their internal theories

The following work chooses particular carriers, operations, observations, or operational semantics. Theorems can be general within those choices without becoming general categorical theorems. In particular, “native” means that actual context/content objects and comparison maps are retained; it does not by itself establish a result for arbitrary contextad/contentad pairs.

- `protocols/plural-semantics/`: several interpretations of result-dependent protocols.
- `protocols/higher-order/`: typed protocols and bounded higher-order interaction.
- `protocols/refinement-recovery/`: contextual comparison and controlled recovery.
- `protocols/law-and-possibility/`: information lost by probability-law semantics and its repair.

#### Feedback and concurrency realizations

**Kernel/writer and shared-world realization.** The [native feedback and shared-content first results](feedback-and-concurrency/native-first-results/README.md) give scoped kernel/writer composition, feedback boundaries and shared-world constructions. They do not complete the extension contract.

**Finite probabilistic realization and its internal theory.** The [retained-boundary refinement and correlation results](feedback-and-concurrency/retained-boundary-refinement/README.md) characterize separator information loss, adaptive coupling refinement, and the limits of uniform comparison witnesses, with explicit context and scheduler assumptions.

**Event/history and local-policy realization.** The [information-and-progress comparison results](feedback-and-concurrency/information-and-progress/README.md) give exact local-information and partner-readiness criteria, fairness transport, and a combined comparison theorem with explicit joint plant and feedback hypotheses.

**Scheduler/control realization and synthesis.** The [constructive local-fairness results](feedback-and-concurrency/constructive-local-fairness/README.md) connect exact finite legal-support synthesis and environmental timing to conditional fairness and controlled completion, without assuming a shared random scheduler.

**Recursive operational-language realization.** The [recursive occurrence machine and finite bridge](feedback-and-concurrency/recursive-occurrence-machine/README.md) supply explicit occurrence jobs, escrowed ownership, ranked-call adaptation and strict operational model maps, with an exact phase-scheduled comparison rather than unrestricted concurrency equivalence.

**Scoped checked-language realization.** The [checked interfaces and claim packages](feedback-and-concurrency/checked-interfaces-and-claims/README.md) supply checked ordinary interfaces, linear claim rights and paired channel packages with written preservation arguments. These structures belong to one operational realization, not to the definition or completion of the general theory.

The kernel/writer construction supplies genuine categorical data and coherence for a specific model. The probabilistic, event/history, scheduler and language results develop that model layer and its interfaces. They should not be counted as a general categorical extension merely because they are reusable or satisfy part of a contract obligation. Conversely, their status as relative examples is not a reason to discard their internal theorems.

A proposed categorical-core extension should state its abstract hypotheses and operations, prove the relevant laws or comparison theorem at that level, and separately show how the chosen realizations satisfy those hypotheses. Until that bridge is proved, model-specific assumptions and conclusions remain visible.

### 3. Applications and worked examples

- `applications/`: the nine-case portfolio and its explicit boundaries, plus a [catalogue of potential applications](applications/potential-applications.md) distinguishing demonstrations, integration work, and research extensions.

A small [stochastic checkpointing example](applications/stochastic-checkpointing/README.md) illustrates retained versus resampled randomness and the importance of correlated observations; it makes no new general theorem claim.

Additional scoped worked examples:
- [Constrained speculative sampling](applications/constrained-speculation/README.md): local legality versus conditioning on successful completion.
- [Retry capabilities and deduplication](applications/retry-capabilities/README.md): adaptive retries, safe retirement, and the state needed for replayable keys.
- [Cost refinement and strategic replacement](applications/strategic-refinement/README.md): when cost improvements preserve strategic best responses.

- [Robot transactions under interference](applications/robot-transactions/README.md): exact compensation and observation-scoped atomicity in a finite known-semantics model.
- [Moving parameter fibres](applications/moving-parameter-fibres/README.md): connection-aware reverse differentiation and the boundary of endpoint-only transport.

- [Finite stochastic feedback](applications/stochastic-feedback/README.md): termination, exit laws, costs and nested elimination.
- [Passive networks](applications/passive-networks/README.md): quantitative boundary response versus connectivity and relational ideal wires.
- [Quantitative doctrine descent](applications/quantitative-doctrine/README.md): lower expectations and capability-preserving finite refinement.
- [Adaptive receipt parallelism](applications/adaptive-receipt-parallelism/README.md): when buffered task executions admit receipt-preserving serial replay.

- [Resource-aware graph witnesses](applications/resource-aware-paths/README.md): Pareto-profile quotients for availability/budget tests, with an exponential representation boundary.

- [Composed accumulator contexts](applications/composed-writer-contexts/README.md): the braid obstruction for independently swapping writer modes and a scope-limited action repair.

- [Verified neural control](applications/verified-neural-control/README.md): exact finite safety certificates and moving admissible parameter fibres under stated model assumptions.

- [Bayesian neural posterior interfaces](applications/bayesian-posterior-interfaces/README.md): exact evidence-update closure for finite-prior linear summaries and horizon-dependent limitations.

These integrate established ideas with the existing framework; they make no new general categorical theorem claim.

The manuscripts contain written proofs at their stated scope. Python checks are finite diagnostics or source checks, not proof-assistant certification. Run checks with Python 3 in their containing directory. Use a disposable copy because several scripts write diagnostic outputs. TeX source checks may require the local manuscript filename as an argument; these do not compile TeX.








