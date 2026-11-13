# 22 — Discriminating probes and unresolved research questions

**Origin:** all of the conversation, especially L518–588, L915–971, L1958–1960, L2441–2631. **Status:** design agenda, **not** a claimed completed theory.

The source supplies an extensive vocabulary, but only some compositional laws. The following probes distinguish rival formalisms efficiently without presuming a single preferred abstraction.

| Unresolved question | Minimal discriminating probe | Implication of a positive or negative result |
|---|---|---|
| Do law changes form an operator action? | Choose two law changes and test associativity/composition and their action on system *morphisms*. | If no coherent operator algebra, index models by parameters/laws rather than forcing an actegory. |
| Can an internal partial action descend to the boundary? | Find two observationally equal states with different definedness or visible outputs. | A counterexample forces richer information-state or relational semantics. |
| Is restriction theory appropriate for this effect? | Test all four restriction axioms for the actual process category; start with nondeterministic branches. | If an axiom fails, do not export \(\bar f\) as a categorical enabledness operator. |
| Does abstract boundary behavior preserve composition? | Assemble two implementations with equal abstraction, including a feedback context. | A distinguishing context requires a finer behavior semantics or narrower allowed contexts. |
| Are component domains enough for global validity? | Keep domains fixed but vary emitted values so downstream preconditions differ. | Failure proves that interfaces need behavior/assumption transfer, not only predicates. |
| Is local solution consistency the real problem? | Construct local sections and test overlap agreement, gluing, and global boundary constraints separately. | Use sheaves only if this local/global mechanism is actually consumed. |
| Are singular solutions or gauge symmetries being lost? | Compare quotient points with different stabilizers or nontransverse constraint loci. | Preserve groupoid/derived data only where those distinctions affect judgments. |
| Does concurrency matter observationally? | Compare interleavings of independent events against a consumer sensitive to causal provenance. | If order/provenance matters, event structure or pomset semantics may outperform plain traces. |
| Do physical ports carry a compositional invariant? | Check power balance under actual interconnection and dissipation assumptions. | A verified energy balance supports Dirac/port-Hamiltonian structure. |
| Does replanning require an executable decision rule? | Present two hidden states with disjoint safe actions and one observation. | Statewise existence is not enough; a uniform observation-based policy is required. |

## Terminology left in reserve

**“Ehresmann spaces.”** The source supplies no precise object. Do not quietly interpret it as an Ehresmann connection, an Ehresmann category, or a differentiable space.

**“Kleisli bicategories of relations.”** Requires a declared base bicategory, higher monad/extension, 2-cells, and effect-composition laws; no unique construction is established by the chat.

**“Causal categories.”** Refers to multiple non-equivalent formalisms. Causal sites are one concrete example, not the canonical definition of every causal category.

**“Vary laws freely.”** Remains typed-hole terminology until allowed law changes, preserved interfaces, and admissible consumers are fixed. There is no meaningful theorem of free variation in a completely unspecified class.

## Next concrete theorem to try

Choose two finite-state components with partial commands and hidden state, let \(\mathsf W\) contain **serial and independent parallel** wiring but initially no instantaneous feedback, and choose external behaviors as history-indexed relations with explicit error outcomes. Define \(\beta\) and prove that it preserves serial and parallel assembly. Add one safety assume/guarantee contract, prove a compositional preservation rule with discharged assumptions, and find a counterexample when the compatibility premise is removed. Then introduce feedback and test whether the original behavior abstraction remains adequate.

This incremental target is deliberately much less general than the source's informal proposed “open restriction equipment.” It exposes the first genuine mathematical obligations rather than presuming the complete architecture exists.

**Related notes:** [20](20-architecture-and-proof-obligations.md), [21](21-small-worked-example.md).
