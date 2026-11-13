# Operational compiler: focused significance audit

29 October 2026. Read `theory/Operational_Certificate_Bridge.md` and `examples/Hidden_Nonlinear_Ring_Discovery.md`. This is a focused comparison, not priority clearance or a full independent proof review.

## Plain-language finding

The operational compiler is a real improvement over the programme's earlier whole-model recognizer: it can search jointly for local mechanisms, component ownership and implementable interfaces before building a complete global transition graph. Its certificates then guarantee the selected model's behavior at every later step. However, the individual engines are established: local simulation equations, finite constraint synthesis, and symbolic inference of all models consistent with observations. The defensible contribution is their explicit integration into the requested decomposition-certificate problem, with shared hidden choices and physical interface restrictions retained. The present evidence does not establish a new general mechanism of control theory or system identification.

## 1. Compositional abstraction is an established baseline

Tabuada, Pappas and Lima, *Composing Abstractions of Hybrid Systems* (2002), define simulations/bisimulations and synchronized parallel composition. Their Theorem 1 proves that suitable subsystem simulations compose into a simulation of the interconnected system; the paper separately analyzes bisimulation and synchronization. The broader literature therefore already covers the principle that local behavior-preserving maps yield a global abstraction when interfaces are respected. [Author-hosted full text, §§2–3 and Theorem 1](https://www.seas.ucla.edu/~tabuada/Papers/HSCC02.pdf).

For the new compiler, U_j is a functional simulation/semiconjugacy equation. W_j makes the assumed input available through actual wiring. The all-time induction, adaptive-controller coupling on a common transcript, and exact conjugacy when all state maps are invertible are elementary consequences of these equations. They are important correctness arguments but should not be marketed as new compositionality mechanisms.

What the compiler adds relative to this baseline is an explicit finite search whose unknowns include the ownership partition, local maps, mechanisms and resource-constrained interface implementation. That is a synthesis/representation contribution. We have NOT established that no earlier compositional synthesis framework supports the same unknowns.

## 2. Bounded synthesis already searches unknown implementations

Finkbeiner and Schewe's *Bounded Synthesis* (2013) searches implementations under finite state bounds using logical constraints, including synchronous/asynchronous distributed systems and additional design constraints. This is an appropriate baseline for turning unknown transition and communication tables into solver variables. [Authors' publication page and abstract](https://rct.cit.tum.de/publications/2013-bounded-synthesis/), [DOI](https://doi.org/10.1007/s10009-012-0228-z).

The present compiler has a different specification: compatibility with observations plus exact component-realization equations, rather than arbitrary LTL implementation synthesis. It should not claim that joint unknown-table solving, finite scope selection, or replacing universal finite-domain checks by a conjunction is a new general technique. Its useful specialization is that the equations attach to requested decomposition witnesses and preserve the identities of hidden sources, mechanisms and interface resources.

## 3. Partial-data Boolean model families have a close existing analogue

Beneš, Brim, Huvar, Pastva and Šafránek, *Boolean network sketches: a unifying framework for logical model inference* (2023), combine partially specified topology and update functions with dynamic restrictions and measured data. Their symbolic procedure computes a compact representation of all compatible Boolean networks. Their discussion explicitly recognizes partially observed variables and explains the relationship to earlier SMT-based abstract Boolean-network inference. [Original article](https://doi.org/10.1093/bioinformatics/btad158), [institutional full PDF](https://research-explorer.ista.ac.at/download/12876/12886/2023_Bioinformatics_Benes.pdf).

Accordingly, keeping unresolved model alternatives, solving for persistent unknown update functions from finite traces, and avoiding an explicit list of all whole models are not new on their own. The nonlinear ring is best classified as exact bounded model abduction combined with subsystem-certificate synthesis. The tested implementation additionally solves ownership conditions alongside those model constraints. Neither the example nor the compiler establishes statistical consistency, physical model adequacy or unique architecture identification.

## 4. Reading the ring example accurately

The data are genuinely partial: five pairs of parity observations do not supply the hidden mode vector or the third core coordinate. The join solver compiles local transition constraints, rather than starting with a list of complete admissible worlds. This fixes the earlier programme's “whole model first” limitation within the declared finite universe.

Nevertheless, the local autonomy criterion is simple dependency closure once the persistent modes are fixed. The fixed ring vocabulary and gate family do substantial work. The example demonstrates simultaneous abductive model/core discovery and refusal to mix incompatible model witnesses; it is not a general hard architecture-recovery benchmark. The two same-world one-bit parents whose intersection requires two bits add a separate operational obstruction, but its proof is the ordinary distinguishability/pigeonhole argument under the stated timing contract.

The exact counts (22 model/state explanations, two seven-witness core alternatives) validate implementation and illustrate ambiguity; they are not themselves the theorem's significance. The more reusable result is the general compilation with local-support checking and honest solver-width dependence.

## 5. What may be claimed in the final report

Recommended central claim:

> We give a finite, exact compiler for jointly discovering candidate mechanisms, component ownership and permitted interfaces from partial observations in a declared bounded operational universe. A satisfying assignment includes explicit local equations that certify the selected decomposition for all future steps of that candidate model. Shared model and source choices are retained across views, so separate possible discoveries are not automatically accepted as jointly realizable. The compiler avoids constructing the full product-state transition table when the actual equation supports are small; solving the resulting constraints can still be expensive.

Recommended novelty wording:

> The constituent mechanisms are established. The contribution here is a programme-specific synthesis and certificate construction that connects partial-view discovery to persistent, resource-accounted operational witnesses. We have not established a novel general identification algorithm or a complete interpretation of this operational calculus in the original graph presentation.

Keep explicit:

- Exact completeness is relative to the declared finite table-witness universe and full Cartesian domains. It is not completeness for all physical implementations or reachable-state-only quotients.
- Searching unknown blocks does not imply an unknown coordinate vocabulary or unbounded latent dimension.
- Small local equation supports make checking avoid the full product state table; they do not guarantee low constraint width or cheap search.
- The source C5 partition quotient and the operational discovery example currently instantiate the certificate framework separately. The operational state-factor boundaries have not been derived from original graph cuts.
- Noninvertible interface changes require a new endpoint-specific feasibility test; no theorem here makes all of them transport exactness.
- One possible-model witness is not a guarantee for the actual environment, nor for every data-compatible environment.

## 6. Remaining substantive theorem burden

The compiler now goes beyond “join arbitrary witness tables”: its U/W/T and ownership factors are explicitly generated from local operational constructors, with a proof of all-time soundness and finite-universe completeness. That passes an important implementation gate. But the original mixed calculus integration remains partial. A stronger later result would derive the operational witness language, its admissible crossings and resource-aware interface transport from a unified presentation, rather than maintaining a separate semantic operational doctrine beside C5. That work should be stated as open, not hidden inside the present success.
