# 21 — Worked finite example: what survives the boundary?

**Status:** derived example, developed to test the chat's proposed interface. **Purpose:** expose the information lost by a hidden-state quotient and by exporting only local restriction predicates.

## Two serial components

Component \(A\) has hidden state \(s\in\{0,1\}\), no input, and a total update that emits \(m=s\) and toggles its internal state:

\[
\delta_A(s)=(1-s,m=s).
\]

Component \(B\) accepts \(m\in\{0,1\}\) only when \(m=0\), and returns `ok`:

\[
\delta_B(0)=\mathrm{ok},\qquad \delta_B(1)\ \text{undefined}.
\]

The serial composite is defined **exactly when \(s=0\)**. Even though \(A\) is total, its output can violate \(B\)'s precondition. Changing \(A\) to \(A'(s)=(1-s,m=0)\) preserves its full definedness domain but makes the composite always defined. Therefore \(\bar\delta_A\) alone does not determine \(\overline{\delta_B\circ\delta_A}\).

## Add an observation boundary

Suppose the external controller sees \(r(0)=r(1)=*\) and does **not** observe \(m\) before issuing a request that runs the series atomically. Its information set is \(B_* =\{0,1\}\). The composite command is **possibly enabled** but **not guaranteed enabled**:

\[
\exists s\in B_*:\ s=0,
\qquad
\neg\forall s\in B_*:\ s=0.
\]

No exact deterministic partial command \(\widehat\delta:*\rightharpoonup\mathrm{ok}\) can represent both internal cases with equality of definedness. If the controller instead can inspect \(m\) **before** invoking \(B\), it has a different protocol and can choose not to invoke \(B\) when \(m=1\). That is an interface change, not a solution to the original atomic-command problem.

## Explicit error semantics changes what is observable

Replace \(B\) by a **total** function returning either `ok` or `Err(input=1)`. The composite is now mathematically total, but still can produce a failure result. A recovery controller can use the diagnostic value; a mere partial function without such a result cannot. If \(A\) already toggled before this error, rollback also requires additional state/protocol data.

## What this one toy establishes

1. **Local valid-domain predicates are not enough for serial assembly.** Outputs matter.
2. **Internal definedness does not automatically descend to readout-level definedness.** Observation fibers matter.
3. **Atomic versus stepwise protocols differ.** Additional observation/control boundaries can improve achievable guarantees.
4. **Partial failure and reported error differ.** Recovery requires knowing intermediate effects.
5. **An architecture must choose the consumers.** A client asking only “might `ok` ever appear?” needs less information than a controller requiring guaranteed completion.

This example is deliberately finite and deterministic: none of these obstructions depends on sophisticated categorical machinery. Any purported general open-system calculus should represent them correctly before claiming support for stochastic feedback, PDEs, or changing physical laws.

**Related notes:** [02](02-preservation-and-substitutability.md), [08](08-restriction-categories.md), [09](09-observation-and-modal-affordances.md), [20](20-architecture-and-proof-obligations.md).
