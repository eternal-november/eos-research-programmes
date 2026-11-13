# 20 — A typed architecture for heterogeneous open components

**Origin:** chat L1958–2013, L2183–2211, L2368–2631. **Status:** **design proposal**. It is not a construction established by the uploaded conversation.

## Build the smallest explicit interface before choosing an ambient category

Fix an allowed wiring syntax \(\mathsf W\) with boundary types \(B\) and composition of diagrams. For each boundary, choose:

\[
\mathsf{Impl}(B)\quad\text{(internal implementations)},
\qquad
\mathsf{Beh}(B)\quad\text{(external behaviors)}.
\]

Supply an interpretation \(\beta_B:\mathsf{Impl}(B)\to\mathsf{Beh}(B)\). If these are **categories**, specify what their arrows are—simulations, parameter changes, refinements, or executable transitions. The conversation uses all these interpretations but never chooses among them. This matters for the type of every categorical formula.

For an allowed wiring \(w:(B_1,\ldots,B_n)\to B\), specify both implementation assembly and behavior assembly. The central proposed law is

\[
\beta_B(\mathsf{Asm}^{\mathsf{Impl}}_w(C_1,\ldots,C_n))
\cong
\mathsf{Asm}^{\mathsf{Beh}}_w(\beta_{B_1}C_1,\ldots,\beta_{B_n}C_n),
\]

with compatibility under nested wiring. Use equality for a strict set-level interpretation, a coherent isomorphism for a suitable categorical one, or a *directed simulation/inclusion* for a sound abstraction. An unqualified \(\cong\) is not an excuse to ignore which observations are retained.

## Four independent proof obligations

**Typing:** every composition has matching ports, state threading, protocol conventions, and clock/resource interfaces. Stateful \(S\times I\rightharpoonup S\times O\) components do not automatically become arrows \(I\to O\) with state forgotten.

**Behavioral preservation:** \(\beta\) is compatible with the chosen wiring. Equivalence of one-step I/O relations may not suffice when feedback is allowed, so the external semantics may need histories, events, or more structured strategies.

**Contract preservation:** for local contracts \(K_i\), state and discharge explicit assumptions. A theorem should look like

\[
\bigwedge_i(C_i\models K_i)
\ \land\ \operatorname{Compatible}_w(K_1,\ldots,K_n)
\implies
\mathsf{Asm}_w(C_1,\ldots,C_n)\models K.
\]

The compatibility predicate must entail resource accounting, information requirements, synchronization, and—where applicable—well-posed feedback. Local validity does **not** imply global validity without it.

**Operational implementation:** decide which mathematical judgments can be computed or monitored, what uncertainties remain, and what control action is issued. A restriction idempotent or a logical theorem need not provide a decision procedure or online controller.

## Placement of the previously discussed tools

- **Coalgebra/behavioral theory:** candidate internal and/or boundary behavior models.
- **Actegory:** transformation of systems by a specified coherent operator algebra, if such an action exists.
- **Fibration/institution:** law/context indexing and satisfaction under change of signature.
- **Restriction category:** partial-process composition where its axioms hold.
- **Predicates/modalities:** contracts, enabledness propositions, temporal, epistemic, strategic judgments.
- **Wiring formalism:** operad/cospan/double-category/polynomial syntax and semantics.
- **Sheaves, event structures, Dirac structures:** extra behavioral geometry when required by locality, concurrency, or power-flow invariants.

These are *possible components*, not a theorem that the product of these abstractions exists or is faithful.

## Explicit stopping condition

A construction is successful only after one realistic component change can be made, its boundary effect computed, assembly rechecked, and at least one nontrivial guarantee proved or falsified. Until then this is a research agenda, not a general-purpose compositional calculus.

**Related notes:** [02](02-preservation-and-substitutability.md), [07](07-wiring-and-open-systems.md), [21](21-small-worked-example.md), [22](22-probes-and-unresolved-questions.md).
