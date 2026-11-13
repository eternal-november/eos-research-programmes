# 13 — Events and causal structure instead of one global state clock

**Origin:** chat L918–946, L1179–1234, L1355–1387. **Status:** retained with definitions and boundary conditions corrected.

## Prime event structures

A common presentation is \((E,\le,\#)\), with a causal partial order \(\le\) and symmetric irreflexive conflict \(\#\), subject to conflict heredity (e.g., \(a\#b\le c\Rightarrow a\#c\)) and often finite-cause requirements. A **configuration** is a conflict-free, downward-closed set of events representing an admissible finite or infinite history. This model retains concurrent alternatives that a single arbitrary linear ordering can obscure. [Winskel's work](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-95.html).

**Example:** event \(a\) authorizes both independent changes \(b\) and \(c\). The configuration \(\{a,b,c\}\) need not privilege the chronology \(a,b,c\) over \(a,c,b\). By contrast, mutually conflicting events \(d\#e\) cannot be in the same configuration.

This is not “dynamics without states”: configurations **are state-like objects**, ordered by inclusion. The value of the presentation is the **provenance of concurrency, conflict, and causality**, not absence of a state space.

## What the event order does and does not encode

Causal precedence is not elapsed time, metric duration, real-time deadline, or a unique global time coordinate. Two unordered events may be concurrent under the chosen semantics, but their concrete implementations can still share a resource and therefore interfere. Event independence must be justified in the modeled operational regime.

Event-structure spans can carry more precise interaction semantics than coarse I/O relations in feedback settings. This is a candidate for preserving concurrency-sensitive substitutability, not a universal replacement for timed transition systems.

## Causal categories and causal sites are not synonyms

Different categorical causality theories have distinct objects and axioms. Christensen–Crane **causal sites**, for example, relate regions through both containment and causal precedence with compatibility requirements; the structure is richer than one causal poset. A relativistic causal ordering can constrain which influences propagate, but **does not by itself generate the dynamics or a deterministic evolution law**.

## When this cut is worth preserving

Use events/causal structures where a linear transition trace forgets essential independence, synchronization, or branching information. Distinguish actual physical causality, causal precedence defined by a model, and causal inference from observational data: their validity stories differ.

**Related notes:** [11](11-feedback-and-trace.md), [19](19-exceptions-and-replanning.md), [22](22-probes-and-unresolved-questions.md).
