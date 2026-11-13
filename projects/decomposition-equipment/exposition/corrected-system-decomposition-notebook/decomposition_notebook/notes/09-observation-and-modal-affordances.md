# 09 — From internal actions to observable capabilities

**Origin:** chat L1435–1441, L1564–1678, L2215–2364, L2635–2737. **Status:** corrected formal bridge and independent derivations.

A controller acts from **information**, not directly from an internal state it cannot observe. Thus actual enabledness, *possible* enabledness, *guaranteed* enabledness, and *known* enabledness should not be silently identified.

Let \(r:S\to O\) be a readout and \(D_a\subseteq S\) the domain of action \(a\). For nonempty current information set \(B_h\subseteq S\) obtained from the complete admissible history \(h\):

\[
\mathrm{May}_a(h)\iff\exists s\in B_h:s\in D_a,\qquad
\mathrm{Must}_a(h)\iff\forall s\in B_h:s\in D_a.
\]

In the usual information-set model, **knowing** that \(a\) is enabled corresponds to the universal condition, assuming the model itself is trusted. Probabilistic confidence, almost-sure truth, adversarial robustness, and statistical detection are distinct semantics.

## Exact observable action: a clean iff criterion

For \(r:S\twoheadrightarrow O\) and a partial deterministic update \(f:S\rightharpoonup S\), an exact partial observation-level map \(\hat f:O\rightharpoonup O\) satisfying \(\hat f\circ r=r\circ f\) exists **if and only if**:

1. **Domain saturation:** \(r(s)=r(t)\Rightarrow (s\in D_f\iff t\in D_f)\).
2. **Output consistency:** if \(r(s)=r(t)\) and both updates are defined, \(r(f(s))=r(f(t))\).

Necessity follows by equality of the domains and outputs of the two partial composites. Sufficiency follows by choosing any representative of each observation fiber, since both definedness and output are independent of the representative. If either condition fails, an exact deterministic observation-level command is not available. Options include belief-state transitions, observation histories, relations, or sound overapproximations—**different interface contracts**.

## An indispensable quantifier distinction for control

\[
\forall s\in B_h\,\exists a:\mathrm{Safe}(s,a)
\quad\not\Rightarrow\quad
\exists a\,\forall s\in B_h:\mathrm{Safe}(s,a).
\]

Two indistinguishable states can each have a different safe action but no single safe action in common. A usable controller must choose its action from observations/history. In multi-step settings, replace an isolated \(a\) by a strategy/policy on available histories and specify the objective (finite reachability, invariance, liveness, discounted performance, etc.).

## The actual modal bridge

For a deterministic partial \(f:X\rightharpoonup Y\) and \(Q\subseteq Y\):

\[
\langle f\rangle Q=\{x\in D_f:f(x)\in Q\},\qquad
[f]Q=(X\setminus D_f)\cup\langle f\rangle Q.
\]

Thus \(\langle f\rangle\top=D_f\), but \([f]Q\) is vacuously true where \(f\) is undefined. Diamond and box coincide **on the domain**, not globally. The slogan \(\bar f=\langle f\rangle\top\) is well-typed only after domain predicates are identified with their corresponding partial identities. Ordinary restriction structure lacks epistemic, temporal, and strategic modalities until extra semantics is specified.

A proof-carrying action can be typed \(\{x:X\mid D_f(x)\}\to Y\) in a compatible refinement-type theory, but a runtime-deciding guard or an arbitrary dependent-type interpretation does not follow just from the existence of \(\bar f\).

**Related notes:** [02](02-preservation-and-substitutability.md), [08](08-restriction-categories.md), [19](19-exceptions-and-replanning.md), [21](21-small-worked-example.md).
