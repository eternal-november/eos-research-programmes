# 01 — What is actually being decomposed?

**Origin:** chat L1435–1441, L1958–1960, L1988–2013, L2279–2306, L2543–2631. **Status:** corrected synthesis; the formal contract below is a proposal.

## The motivating problem

The target is **not** a classifier that maps an environment property to a mathematical object. It is an open-system architecture in which subsystems can have *different internal mathematical representations*, while their external interaction and the guarantees that survive assembly are explicit.

The key question is: *what may an environment, controller, verifier, or other subsystem infer and do through the boundary of a component?* A state-space dimension, input/output signature, or collection of formulas alone cannot answer it.

A component specification can be organized as

\[
C=(B,S,H,I,U,Y,\delta,r,\mathsf{Fault},\mathsf{Spec}),
\]

where **B** is an interface type (possibly carrying time and protocol structure); **S** an internal state carrier; **H** admissible histories; **I** initial-state assumptions; **U** commands/inputs; **Y** externally visible results; **δ** transitions (a map, relation, kernel, or continuous dynamics); **r** observation/readout; **Fault** explicitly observable or modeled failures; and **Spec** designated safety, liveness, resource, and performance requirements. This is a *checklist*, not a universal mathematical definition: types and some fields depend on the domain.

## Three different tasks

1. **Decomposition:** break a system into open components and give compatible assembly operators. The pieces need not retain all details of the original presentation, but collectively must reconstruct the selected behaviors or guarantees.
2. **Variation:** change a component's law, observation, state, model, or internal decomposition. Its boundary contract may change; identify and revalidate affected consumers.
3. **Substitution:** replace a component without violating a *declared* external contract in *specified* contexts. Contextual equivalence or refinement is required, not identity of implementation or of all restrictions.

The original chat drifted between (2) and (3). “Vary laws freely” is appropriate only in the sense of *permitting well-typed changes* and propagating their effects. “Preserve the whole boundary semantics” defines a much narrower substitution problem.

## Separate semantic facets before choosing theory

| Facet | Example question | What it cannot be replaced by |
|---|---|---|
| Carrier | What states/configurations exist? | Observation classes |
| Evolution | What successor behavior is possible? | An ordering on states |
| Information | What can be inferred from available measurements? | Actual state truth |
| Enabledness | Where is a particular command defined? | Safety or a computable guard |
| Outcome/fault | Does failure block, return error, crash, or change state? | Undefinedness alone |
| Specification | What is required, allowed, forbidden, optimized? | A mathematical domain without a task law |
| Assembly | Which compatible components can be connected? | A proof that their guarantees compose |

These are **interacting interfaces**, not independently selectable tensor factors. A consumer of composition, verification, control, or audit can force finer distinctions than the initial model designer anticipated.

## Criterion of success

A representation is adequate if every designated consumer has a sound way to answer its questions using the boundary data and the assembly rules. A reduction is justified only relative to those consumers. If two hidden states are merged but admit different actions, an observation-only controller cannot automatically inherit a state-aware plan.

**Failure condition:** treating a typed connection, a valid local transition, and a global guarantee as equivalent claims. They are three separate obligations.

**Related notes:** [02](02-preservation-and-substitutability.md), [07](07-wiring-and-open-systems.md), [20](20-architecture-and-proof-obligations.md).
