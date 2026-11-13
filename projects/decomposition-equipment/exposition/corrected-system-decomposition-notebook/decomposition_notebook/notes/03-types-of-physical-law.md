# 03 — “Physical law” is a role-indexed family, not one operator type

**Origin:** chat L444–514 and L465–500. **Status:** source-derived taxonomy with corrections.

The early actegory discussion correctly rejects a universal category of *laws*. A law may describe **evolution, admissibility, selection, symmetry, constitutive response, or interconnection**; these have different types. Even the same written equation may be used in several roles, depending on what variables are taken as inputs, states, controls, or observations.

| Law role | Minimal mathematical shape | What must be supplied to get behavior |
|---|---|---|
| Evolution map | \(f:S\to S\), or \(T:S\times U\to S\) | Time convention, enabled actions, solution or iteration |
| Infinitesimal generator | \(v:S\to TS\) | Existence/uniqueness or differential-inclusion solution semantics |
| Constraint | \(R\subseteq X\times Y\) or equation \(F(x,y)=0\) | Which variables are solved for, feasibility, possible multiplicity |
| Variational principle | Functional \(\mathcal A:\mathrm{Paths}\to\mathbb R\) | Variation class, boundary data, extremality/stationarity rule |
| Symmetry | Action plus invariance/equivariance judgment | Which object is transformed and which quantities are invariant |
| Conservation | \(I:S\to V\), with \(I(\phi_t(s))=I(s)\) | Existence of trajectories; proof of invariance |
| Constitutive | Response relation between efforts, flows, strains, etc. | Coupling to balance laws and boundary conditions |
| Wiring/coupling | Typed composition of ports and constraints | Existence and well-posedness of composite system |
| Measurement | Observation map/kernel and sensor protocol | Noise, calibration, information structure |

The table classifies **mathematical role**, not the scientific provenance or ultimate validity of a theory.

## Why an actegory is conditional here

An actegory requires not only a family of operations but a monoidal algebra of those operations, functorial action on system objects *and arrows*, and coherent interaction. Vector fields do not automatically furnish it: a collection of fields parameterizes potential dynamics, while their flows need not commute, exist globally, or respect an imagined tensor product of laws.

A law such as \(F(x,y)=0\) is often better treated relationally. If solving for \(y\) is unique and well-posed, it *may* induce a map. That step is not invertible: it loses information about solution multiplicity or the variables no longer exposed. A Hamiltonian requires a Poisson/symplectic structure to generate dynamics, and a Lagrangian requires an admissible variation/geometry, not just a law-object acting on arbitrary systems.

## A useful comparative experiment

Fix one circuit network topology and compare three variants: (i) change only component parameters, (ii) replace a constitutive relation by a multivalued one, (iii) change the interconnection pattern. The first is often an indexed parameter change; the second can alter the type of process semantics; the third changes wiring. Requiring all three to be “the same law action” obscures the actual changes and their verification costs.

**Related notes:** [04](04-actegories.md), [06](06-indexing-institutions-doctrines.md), [16](16-dirac-and-implicit-physical-systems.md).
