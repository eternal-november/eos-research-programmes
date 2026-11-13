# 14 — Diffeological and Frölicher spaces: smoothness without manifold charts

**Origin:** chat L976–994, L1059–1110. **Status:** source idea retained; mathematical claims calibrated.

## Two different generalized smooth structures

A **diffeological space** is a set \(X\) supplied with designated *plots* \(p:U\to X\), where \(U\) ranges over open subsets of Euclidean spaces. Constants are plots; smooth reparameterizations of plots remain plots; and locally compatible plots glue as plots. A map \(f:X\to Y\) is smooth if it takes plots of \(X\) to plots of \(Y\) by composition. This gives useful subset, quotient, product, and function-space constructions even when the resulting objects are not ordinary finite-dimensional manifolds. [Iglesias-Zemmour](https://doi.org/10.1090/surv/185).

A **Frölicher space** is presented using mutually determining classes of smooth curves \(c:\mathbb R\to X\) and smooth real-valued functions \(\varphi:X\to\mathbb R\), constrained by smoothness of \(\varphi\circ c\). The two theories are related but **not definitionally identical**. Plot-side smoothness and function/curve-side smoothness preserve different primitive information.

## Decomposition payoff

The carrier \(X\) and its smooth structure can be changed without first assuming a compatible atlas of ordinary manifold charts. This is useful for spaces of maps/fields, quotient state spaces, singular orbit spaces, or nonstandard smooth parameter spaces. The gain is a better **substrate for expressing laws**, not a law generator.

It is tempting to say that choosing a diffeology automatically gives well-defined tangent bundles, vector-field flows, or a smooth hybrid controller. It does not. Several inequivalent tangent constructions are possible for generalized spaces, and existence/uniqueness of dynamical solutions still requires hypotheses. A space with mixed discrete and continuous modes also needs a **hybrid execution semantics**; smooth plots alone do not define resets or jump admissibility.

## Example discrimination

If quotienting a manifold by symmetries produces a singular space on which the *quotient of smooth observations* remains meaningful, diffeological methods may be more faithful than forcing the quotient into a manifold structure. If the task is only finite-state reachability, this extra smooth machinery contributes no necessary control operation.

**Terminology reserve:** the source says “Ehresmann/Frölicher/diffeological spaces.” “Ehresmann space” was not specified and cannot be repaired without a definition; it could point toward several different Ehresmann-associated constructions. It is not part of this note's asserted equivalence.

**Related notes:** [15](15-weil-jets-and-pde-geometry.md), [17](17-gauge-and-derived-solution-spaces.md).
