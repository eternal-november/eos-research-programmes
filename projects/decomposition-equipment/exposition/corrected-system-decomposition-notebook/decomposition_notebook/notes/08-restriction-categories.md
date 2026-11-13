# 08 — Restriction categories: the algebra of *definedness*

**Origin:** chat L998–1055, L1435–1703, L1958–2118, L2635–2737. **Status:** definition corrected and boundaries identified.

## The actual structure

For a partial function \(f:X\rightharpoonup Y\), the restriction \(\bar f:X\rightharpoonup X\) is the partial identity on the domain \(D_f\). In a restriction category, each arrow is supplied with such an idempotent, satisfying (with usual right-to-left composition):

\[
\begin{aligned}
f\bar f&=f,\\
\bar f\bar g&=\bar g\bar f\quad(\text{common source}),\\
\overline{g\bar f}&=\bar g\bar f\quad(\text{common source}),\\
\bar g f&=f\,\overline{gf}\quad(\text{composable }f,g).
\end{aligned}
\]

These axioms are *algebraic*. They do not introduce a new computation that decides where an arbitrary partial program terminates. The restriction operation is part of the chosen category's structure. For split restriction categories there is a representation by categories of partial maps, with appropriate domain-monic data. See [Cockett–Lack](https://www.sciencedirect.com/science/article/pii/S0304397500003820).

## The precise compositional gain

For partial functions,

\[
D_{gf}=D_f\cap f^{-1}(D_g).
\]

A downstream precondition must be pulled back through the **actual upstream behavior**. Two total functions with identical domains but different outputs can yield different composite domains. Let \(f_0(*)=0\), \(f_1(*)=1\), and let \(g\) be defined only at \(0\). Then \(gf_0\) is total and \(gf_1\) nowhere defined. Thus **domains alone are not a sufficient interface for composition**.

For independent Cartesian products, \(D_{f\times g}=D_f\times D_g\); shared resources or feedback require more semantics and may defeat this independence.

## Five tempting but false identifications

1. \(\bar f\) is not a total Boolean-valued `enabled?` method. In effectful or computable settings, producing a restriction result may itself diverge.
2. Definedness is not safety. An unsafe state transition can be total, and a safe admissible evolution may be only locally defined.
3. Undefinedness is not a returned diagnostic: \(f:X\rightharpoonup Y\) differs from \(f:X\to Y+E\), which reports typed errors; blocking, crash and partial side effects need further structure.
4. A physical law's *approximation regime* is not necessarily the domain of its mathematical function. Defining \(\bar f\) to capture regime validity is a **chosen restriction**, not an automatic property of an equation.
5. An internal \(\bar\delta:S\times I\to S\times I\) does not automatically induce a boundary \(\bar C:I\to I\). Hidden state must be dealt with first.

## A structural obstruction for nondeterminism

Let \(R(x)=\{0,1\}\) and let \(g\) be defined only on \(0\). If \(\bar R\) means identity on *existentially enabled* inputs, then \(\bar g\circ R\) retains only the \(0\)-branch, but \(R\circ\overline{g\circ R}\) retains both branches. The last restriction axiom fails. Arbitrary relations cannot receive this naive existential-domain restriction structure.

## Useful extent

Restriction categories are appropriate when the *chosen process composition* has the required partiality laws. They are not a universal feasibility checker, safety calculus, or modal logic. Related modal predicates can be built over a compatible predicate semantics; see [09](09-observation-and-modal-affordances.md).

**Related notes:** [07](07-wiring-and-open-systems.md), [09](09-observation-and-modal-affordances.md), [19](19-exceptions-and-replanning.md).
