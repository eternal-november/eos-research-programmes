# 12 — Local-to-global behavior: presheaves, sheaves, and stacks

**Origin:** chat L682–683, L846–865, L934–935, L1439–1441. **Status:** common categorical errors corrected; application examples expanded.

A sheaf should be chosen because the system genuinely has **local data on overlapping domains whose compatibility and gluing matter**. It is not a mandatory upgrade from partial observability, nonstationarity, or distributed execution.

## The typed construction

For a topological space \(X\), a presheaf of sets is \(F:\mathsf{Open}(X)^{op}\to\mathbf{Set}\). For \(V\subseteq U\), the arrow \(F(U)\to F(V)\) is a **restriction map**, not a time-evolution map from an earlier time to a later time. A sheaf requires compatible sections on a cover of \(U\) to glue **uniquely** to a section of \(F(U)\).

A typical application is a sheaf of solutions of a local differential equation on a fixed geometric domain: solutions restrict to smaller open sets, and agreeing smooth solutions glue. Boundary conditions or global consistency constraints can be represented, but may introduce additional structure or restrict admissible global sections.

## Three logically different obstructions

1. A chosen family of local sections **disagrees on overlaps** and therefore cannot glue.
2. Local solutions on some domains exist but **no global solution of the selected constrained problem** exists.
3. A particular partial solution **cannot extend** into a specified larger domain.

None implies an empty stalk. A stalk summarizes germs near a point; global obstruction can arise while all local stalks are nonempty. Conversely, an empty section over one domain may arise from constraints unrelated to a local singularity.

**Toy witness:** constant-valued local solutions \(s_1\equiv0\) on \((-1,0.2)\) and \(s_2\equiv1\) on \((-0.2,1)\) disagree on their overlap. This family cannot glue, even though globally constant solutions exist. Thus “incompatible local choices” and “no global model” are distinct.

## When a stack is genuinely required

A set-valued sheaf forgets automorphisms of local objects. A stack can retain groupoid-valued data and coherent descent up to isomorphism. This is significant for gauge-related field configurations, bundles, or moduli problems, where locally equivalent presentations may need transition isomorphisms satisfying cocycle conditions. **Merely having many agents or heterogeneous data does not force a stack.**

## What gluing does *not* do

It neither finds local sections, proves computability, synthesizes a feasible trajectory, minimizes cost, nor licenses arbitrary forward extrapolation. Replanning via “choose a new local section and glue” is valid only if the new sections exist, agree on overlaps, satisfy boundary/history constraints, and support the desired objective. The relevant solution sheaf must have been constructed.

**Related notes:** [15](15-weil-jets-and-pde-geometry.md), [17](17-gauge-and-derived-solution-spaces.md), [20](20-architecture-and-proof-obligations.md).
