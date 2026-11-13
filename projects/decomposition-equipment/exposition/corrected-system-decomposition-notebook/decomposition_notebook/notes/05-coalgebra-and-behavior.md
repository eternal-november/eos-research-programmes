# 05 — Coalgebra versus behavior-first system modeling

**Origin:** chat L665–721 and L918–958. **Status:** retained, sharpened, and expanded.

These offer two different cuts through “state plus dynamics.” They should be kept as alternatives, not merged into a supposed general ladder.

## Coalgebra: explicit state with an abstract behavior signature

An \(F\)-coalgebra is \(c:X\to F(X)\), for a specified endofunctor \(F\). The functor fixes the *one-step behavioral shape*; the coalgebra map specifies a particular system. Examples include \(F(X)=Y\times X\) for output streams and \(F(X)=(Y\times X)^U\) for a total deterministic input-driven Mealy machine. Powerset-like and distribution functors model selected forms of branching or randomness under their respective categories and size/measure restrictions.

Coalgebra exposes tools such as behavioral equivalence and bisimulation when suitable final coalgebras or relation liftings exist. It does not supply observation semantics, control objectives, or a wiring calculus automatically; also, different choices of \(F\) are materially different model classes.

## Willems-style behavioral systems: do not privilege input/output or state

A behavior-first system is a set of admissible trajectories

\[
\mathcal B\subseteq W^T.
\]

Here \(W\) is a signal-value space and \(T\) a time or indexing set. Differential equations, algebraic relations, and network constraints *select* the behavior. Inputs and outputs may be designated later rather than being intrinsic. This is the essential antidote to automatically converting every law to \(x_{t+1}=f(x_t,u_t)\). [Willems, behavioral approach](https://citeseerx.ist.psu.edu/document?doi=12e43968c77466cfbd4720f2651220a9d7a5e365&repid=rep1&type=pdf).

### Composition by constraints and hiding

For two behaviors sharing a signal \(z\), the composed behavior can be written

\[
\mathcal B_{AB}=\{(x,z,y): (x,z)\in\mathcal B_A,\ (z,y)\in\mathcal B_B\}.
\]

If \(z\) is internal, hide it through projection:

\[
\mathcal B_{\mathrm{ext}}=\{(x,y):\exists z\ (x,z,y)\in\mathcal B_{AB}\}.
\]

This is a powerful mathematical decomposition: interconnection is constraint intersection/join, and encapsulation is existential elimination. But existential hiding can lose uniqueness, causality, diagnostic information, or the feasibility of online implementation. A behavior as a set of traces also does not by itself identify controllable versus uncontrollable coordinates.

## Selection test

If the scientific law is primarily an equation constraining *whole trajectories* (DAE/PDE, reciprocal or multivalued physical response), behavior-first modeling may preserve more meaning than forcing a direction of computation. If the question requires algorithmic state update, a coalgebra/state representation may be preferable or may be derived from the behavior under realization hypotheses. Neither automatically subsumes the other at the level of computational interfaces.

**Related notes:** [03](03-types-of-physical-law.md), [07](07-wiring-and-open-systems.md), [15](15-weil-jets-and-pde-geometry.md).
