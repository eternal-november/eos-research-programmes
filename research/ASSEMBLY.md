# Instance assembly and checked refinement maps

Status: program integration in progress. The general definitions and proof laws are in [THEORY.md](THEORY.md) and [Execution.lean](Execution.lean); this file instantiates them rather than treating a common vocabulary as an assembly proof. [assembly_model.py](assembly_model.py) independently checks the implemented maps at the finite scopes stated below. Mathematical support and repository acceptance remain separate.

## A-D: the actual digital protocol in the common core

The source state is the operational Prefix from digital_model.py: fixed fault index, leader input, epoch and the complete admitted event prefix. The local-history map is local_view, and the correct policy is local_action. The transition is successors, whose guards admit signing, delivery and cutoff choices independently of the agreement or certificate conclusion. A fixed fault index selects which actor components must follow the correct policy. The source action domains are finite tagged proposal, echo, terminal, wait, retain and observe commands; faulty commands are represented by the admissible normalized signature/delivery choices. Invalid-byte traffic and processing-resource limits remain the digital module's declared channel boundary.

The source is a fixed-policy closed loop, not a synthesis oracle. The common-core embedding gives each participant its actual local policy and regards the generator's remaining choices as adversarial transitions. The issued command is extracted independently from each generated edge: proposal masks from raw events, each follower's actual outgoing echo from its routed echo event, terminal masks from actual signature events, and the explicit wait/retain/observe actions in the remaining phases. The adapter checks every correct issued command against the policy applied to that actor's previous local history. No fault index or future event is supplied to that policy.

The target state is DigitalState in assembly_model.py. It carries the current fault/input/epoch/phase context, raw/echo/signature/decision/receipt facts and the persistent local records. Its enabled events and factual updates are implemented independently by abstract_digital_events and abstract_digital_step; neither calls the source successors or filters outcomes by agreement. The projection alpha reads the corresponding facts and local records from the source prefix.

For actor i, the history map h_i and action lift are identity on the preserved local records and tagged commands. The analytic action projection is likewise identity. The fault index is unchanged. The common-core refinement obligations are instantiated as follows.

| Obligation | Witness |
|---|---|
| Initiality | The seven source initial contexts project to the same fault/input/empty-event target contexts. |
| Observation correspondence | Each target local-record component equals local_view(source,i). The adapter checks this at every generated point. |
| Local implementation | Equal correct local views across all fault contexts yield the same local_action; the adapter constructs 586 local policy classes. It also compares actual edge-issued commands, rather than merely calling the policy twice. |
| Successor correspondence | For every source point, the set of projected source successors equals the target's independently generated successor set. Both directions are checked. |
| Fault/time preservation | Every edge retains the same fault and epoch and advances the same observable event stage. The logical round-clock annotation is retained separately from the event count. |
| Property decode | Decision, signing, receipt, certificate and historical entry facts are retained exactly. D2/D3 establish the abstract agreement, validity and evidence properties; equality transports them back. |
| Execution existence | Every nonterminal source and target point has a successor. The sole one-slot terminal phase is explicitly successful and is not used to certify recurring service through an empty run set. |

The complete finite audit covers 66,329 source states, 66,322 guarded edges and 265,548 correct action occurrences. Alpha is bijective on this generated fragment, and successor images agree. This is stronger than one-way trace inclusion for this particular representation, but does not establish equivalence with another Byzantine protocol or with unmodeled network behavior. The kernel is the earlier validated-batch normalization, not a newly invented state-only projection.

The generic theorem local_policy_factorization explains why the checked finite action classes yield a single local policy table. The explicit local_action function is already a compact realization of that table. refinement_maps_run and refinement_transports_property then apply to the constructed local/transition correspondence; their application is a derived mathematical adapter justified by the exhaustive finite certificate and source-level guard inspection. The Python source generator and target updater are not themselves mechanically extracted from Lean, and no such stronger implementation-verification claim is made.

### Termination, repetition and time

One slot has a successful finite verdict at its terminal cutoff. It can either be embedded into the common core with a marked clocked terminal stutter for that finite mission, or be followed by a new epoch. Unexpected earlier termination receives a failure verdict; ordinary prefixes are not maximal executions.

Sequential repetition retains the same fault identity and immutable committed history, advances the epoch tag, and provides a fresh leader input. The local history adapter to the per-slot policy takes the suffix beginning with the newest epoch marker. This is essential: applying the per-slot phase computation to an unsliced concatenation of old and new records would confuse old phase markers with the current phase. The suffix operation is actor-local; it supplies no information about faulty identities. Old messages cannot re-enter the new slot because epoch validation is part of admission.

The preserved service claim is one completed entry per three logical rounds, with decision at round two and public evidence at round three. The extra inside-round delivery observation is an event point, not an additional elapsed round. An event-counter safety/refinement theorem alone is therefore not a proof of that rate: the source and target retain the same round-clock annotation and cutoff schedule. There is no assertion of a physical seconds-per-round bound or an overlapping-slot throughput improvement.

For arbitrary repetition, induction uses D2 agreement and correct-leader validity on each legal fresh slot; the append operation preserves earlier entries. Digital.lean proves the corresponding unbounded ledger equalities. The finite same-fault two-slot checks supplement that induction. No new independent faulty set is selected on each epoch.

### Epistemic versus strategic transport

Because the target retains the same event alternatives and local records, the digital module's event-product comparison preserves Boolean/nested-knowledge queries over tracked facts. Complete guarded histories also preserve fixed-protocol temporal statements and branching historical-slot finality. These judgments use the same source executions, not the former independent delivery example.

This adapter does not infer strategic equivalence from epistemic equivalence. Its policy is fixed and independently checked. Replacing the protocol or synthesizing different actor commands activates the whole-prefix prescription and local-refinement obligations again. The distinction is material: the earlier hidden-state continuation example fails despite its one-step safe state projection.

## Remaining assembly work

The witnessed/timed and institutional/recovery modules have been integrated as mathematical contributions, but their current-context adapters and review repairs remain active work. In particular, valid share filtering must precede identity deduplication; finite measurement messages need a total quantizer contract; schedule snapshots must be canonical; and report-age and reset conditions must agree with the continuous proof.

Zero-delay reduced-capacity recovery is not automatically an instance of the timed uniform-mode theorem. A delayed recovery must retain outstanding authorized commands, drain/revalidate the FIFO before reducing capacity, and establish a live-safe pending tube before releasing isolation. A separate constructive drain/repair/recenter/warmup extension is under development. Until its proof and implementation are integrated, no combined continuous-recovery guarantee is asserted.

This file will receive the remaining explicit maps and compatibility results before a program-level completion audit. Naming these obligations is not their discharge.
