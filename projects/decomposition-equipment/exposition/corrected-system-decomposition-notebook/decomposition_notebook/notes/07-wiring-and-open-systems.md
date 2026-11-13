# 07 — Wiring formalisms: interfaces, assembly, and hidden state

**Origin:** chat L665–693, L761–799, L1958–2013, L2088–2211. **Status:** architecture retained, typing corrected.

The salient problem is **not** just decomposing a large equation into smaller ones. It is defining a syntax of connections, an interpretation of components, and rules for eliminating/hiding internal interface variables without losing required guarantees.

## Distinguish four layers

**Typed boundaries:** which ports exist and what they carry; possibly including signal direction, protocols, clocks, units, energy ports, or resource capabilities.

**Component behavior:** what an attached subsystem does, or which histories it permits, for those boundary variables.

**Wiring operation:** how external and internal boundaries are connected, synchronized, duplicated, identified, or hidden. This requires typing and may require copying/deleting structure absent from general monoidal categories.

**Contract composition:** which assumptions, guarantees, and failures survive the wiring operation. This does not follow merely from the syntax being well-typed.

## Several legitimate syntaxes

- **Decorated cospans:** a span-like interface shape \(X\to N\leftarrow Y\) in which the apex carries a decoration (e.g., a graph or dynamical structure); composition generally uses pushouts plus compatible decoration operations.
- **Structured cospans:** maps \(L(X)\to N\leftarrow L(Y)\), where a functor \(L\) chooses how interface objects embed as internal structures. This is a different construction, not just another name for decorated cospans. [Baez–Courser](https://arxiv.org/abs/1911.04630).
- **Polynomial interfaces:** dependent input/output shape can capture choices of positions and directions; a composition semantics for the particular polynomials must still be supplied.
- **Double categories/equipment:** distinguish horizontal systems or proarrows from vertical interface maps/refinements; 2-cells encode compatibility. Neither direction has a canonical physical interpretation until defined.
- **Operads/colored operads:** express a syntax of hierarchical plugging; an algebra of the operad provides the semantic operations.

## Minimal typed assembly contract

Let \(w:(B_1,\ldots,B_n)\to B\) be an allowed wiring. An interpretation needs operations

\[
\mathsf{Asm}_w:\mathsf{Comp}(B_1)\times\cdots\times\mathsf{Comp}(B_n)\to\mathsf{Comp}(B),
\]

compatible with nested wiring and identities, strictly or up to coherent isomorphism. If \(\mathsf{Comp}(B)\) is a **category**, the action of wiring on component morphisms/refinements must be specified too. The conversation's \(\mathcal R_B\) alternately denoted processes as arrows and systems as objects; that ambiguity destroys the types of its assembly formulas.

For internal stateful components \(f:S_A\times I\rightharpoonup S_A\times M\) and \(g:S_B\times M\rightharpoonup S_B\times O\), serial composition carries the product state \(S_A\times S_B\). It is defined when \(f\) runs **and its particular output** lies in the domain of \(g\). Local domains alone are insufficient (see [08](08-restriction-categories.md)).

## What remains separate

Wiring may be possible without solving an instantaneous feedback equation. It may be semantically defined but unsafe under an energy budget. Local contracts may conflict when hidden states share an unmodeled resource. An assembly theorem needs explicit compatibility and observation assumptions.

**Related notes:** [05](05-coalgebra-and-behavior.md), [08](08-restriction-categories.md), [11](11-feedback-and-trace.md), [20](20-architecture-and-proof-obligations.md).
