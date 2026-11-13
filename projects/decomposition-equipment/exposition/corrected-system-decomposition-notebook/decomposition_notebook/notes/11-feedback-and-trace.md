# 11 — Feedback is an operation with its own existence and coherence obligations

**Origin:** chat L918–927, L1988–2009, L2493–2539. **Status:** corrected; counterexamples derived.

Not every notion of wiring includes feedback. Even when there is a diagrammatic loop, its semantics could mean an instantaneous algebraic constraint, a delayed update, an infinite interaction trace, a fixed point, or a stateful protocol. Those interpretations are not interchangeable.

## Instantaneous feedback as a relation

Take \(F:X\times U\rightharpoonup Y\times U\). One possible semantics is

\[
(x,y)\in\operatorname{Fb}(F)
\iff\exists u\in U:\ F(x,u)=(y,u).
\]

This is a **relation**, not necessarily a partial function. With \(X\) a singleton and \(Y=U=\{0,1\}\):

- \(F(*,u)=(u,1-u)\) has no feedback solution.
- \(F(*,u)=(u,u)\) has two external outcomes.

Existence of a fixed point does not establish a deterministic closed-loop update. Uniqueness of the internal fixed point suffices, but is not necessary, for an unambiguous external result: several internal solutions may share the same visible output.

## A delayed loop is not an algebraic fixed point

A recurrence \(u_{t+1}=h(u_t)\) with a specified initial state is well-defined even if \(h\) has no fixed point or its trajectories oscillate. Treating oscillation as undefinedness confuses liveness/stability/specification failure with mathematical nonexistence. For continuous-time feedback, causal well-posedness can require existence, uniqueness, regularity, and non-Zeno conditions, depending on the model.

## Traced categories and partial traces

A traced symmetric monoidal category supplies a trace \(\operatorname{Tr}^U_{X,Y}:\mathcal C(X\otimes U,Y\otimes U)\to\mathcal C(X,Y)\) obeying trace axioms. **Its presence is additional structure**, not guaranteed by a restriction category or cospan syntax. “Trace defined only for some arrows” is different from “a total trace produces an arrow representing a partial function.” For a formal partially traced structure, see [Malherbe–Scott–Selinger](https://arxiv.org/abs/1107.3608).

The \(\mathrm{Int}\) construction and geometry-of-interaction approaches are useful where feedback/interaction itself is primitive. Their categorical feedback is not automatically physical time evolution, numerical iteration, or control-theoretic stability.

## A concrete abstraction obstruction

A coarse external relation \(R\subseteq I\times O\) may be adequate for one-shot composition but inadequate for feedback contexts. In nondeterministic dataflow, processes with the same ordinary I/O relation can have different feedback behavior. The relevant abstraction must preserve the timing/causal dependency of interactions, not just a set of possible input/output pairs. See Saunders-Evans and Winskel, *Event Structure Spans for Nondeterministic Dataflow* (author-hosted research cited in the earlier audit).

**Selection condition:** choose the loop semantics first. Only then ask whether a trace, relation, fixed-point operator, guarded recursion, or temporal transition system implements it faithfully.

**Related notes:** [02](02-preservation-and-substitutability.md), [07](07-wiring-and-open-systems.md), [13](13-events-concurrency-causality.md), [20](20-architecture-and-proof-obligations.md).
