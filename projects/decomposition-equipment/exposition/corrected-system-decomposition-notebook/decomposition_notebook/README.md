# Corrected decomposition notebook

**Source:** the uploaded AI conversation `Pasted text(20261027-151133).txt` (chat line references run L1–L2737). **Purpose:** turn an exploratory dialogue into usable notes, not preserve its chronology, assistant confidence, or original taxonomy. **Coverage:** 23 independent notes; law operators, constraints, behavioral modeling, internal/boundary composition, modalities, failure, generalized smoothness, concurrency, geometric mechanics, and a concrete development path.

## Start here by interest

| Problem / consumer | Relevant notes | Non-negotiable caveat |
|---|---|---|
| Define the system decomposition and interfaces | [01](notes/01-problem-and-semantic-interface.md), [20](notes/20-architecture-and-proof-obligations.md) | No unconditional theorem that local validity implies global validity |
| Preserve semantics under abstraction or replacement | [02](notes/02-preservation-and-substitutability.md), [21](notes/21-small-worked-example.md) | Equality of I/O types is insufficient; which contexts observe behavior? |
| Factor laws out of system models | [03](notes/03-types-of-physical-law.md), [04](notes/04-actegories.md), [06](notes/06-indexing-institutions-doctrines.md) | A family of laws is not automatically a monoidal action |
| Avoid a state-space bias | [05](notes/05-coalgebra-and-behavior.md), [10](notes/10-relations-allegories-and-effects.md) | Behavior as a relation may lose implementation and causal information |
| Compose open systems | [07](notes/07-wiring-and-open-systems.md), [11](notes/11-feedback-and-trace.md) | Feedback requires its own semantic rules and often well-posedness |
| Express partial operations and observer-visible capabilities | [08](notes/08-restriction-categories.md), [09](notes/09-observation-and-modal-affordances.md) | Definedness is neither decidability nor knowledge nor safety |
| Local/global consistency and solution moduli | [12](notes/12-sheaves-and-stacks.md), [17](notes/17-gauge-and-derived-solution-spaces.md) | Gluing and derived data do not synthesize trajectories |
| Model non-global time and concurrency | [13](notes/13-events-concurrency-causality.md) | Causal order does not supply metric time or evolution |
| Model non-manifold states or differential laws | [14](notes/14-diffeology-and-frolicher.md), [15](notes/15-weil-jets-and-pde-geometry.md) | Smoothness/infinitesimal data does not imply well-posed dynamics |
| Model energy/implicit physical laws | [16](notes/16-dirac-and-implicit-physical-systems.md) | Energy balance is not global solvability, stability, or reversibility |
| Model bidirectional information/incentives | [18](notes/18-lenses-games-and-interactions.md) | A backward channel does not automatically mean controller, gradient, or equilibrium |
| Model exceptions, reachability, and replanning | [19](notes/19-exceptions-and-replanning.md) | Composition is not plan synthesis |
| Decide what to test/build next | [22](notes/22-probes-and-unresolved-questions.md), [23](notes/23-other-techniques-in-reserve.md) | A concept's existence is not an application theorem |

## Recommended reading sequences

**Shortest path to the original research idea:** 01 → 02 → 07 → 08 → 09 → 20 → 21 → 22. This gives the typed boundary problem and the main obstructions before introducing specialized machinery.

**Law/model factorization:** 03 → 04 → 06 → 05 → 15 → 16. This retains the distinction between law as operator, equation, index, generator, and physical constraint.

**Less conventional techniques:** 10 → 11 → 13 → 14 → 15 → 16 → 17 → 18 → 23. Each note states both a genuine mathematical payoff and what the apparatus does *not* automatically imply.

## Standalone notes

<!-- BEGIN MANIFEST -->
- [01 · What is actually being decomposed?](notes/01-problem-and-semantic-interface.md)
- [02 · Preservation, observational equivalence, and the cost of quotienting](notes/02-preservation-and-substitutability.md)
- [03 · “Physical law” is a role-indexed family, not one operator type](notes/03-types-of-physical-law.md)
- [04 · Actegories separate operator algebra from carrier semantics](notes/04-actegories.md)
- [05 · Coalgebra versus behavior-first system modeling](notes/05-coalgebra-and-behavior.md)
- [06 · Fibrations, institutions, and doctrines: three different law/parameter interfaces](notes/06-indexing-institutions-doctrines.md)
- [07 · Wiring formalisms: interfaces, assembly, and hidden state](notes/07-wiring-and-open-systems.md)
- [08 · Restriction categories: the algebra of *definedness*](notes/08-restriction-categories.md)
- [09 · From internal actions to observable capabilities](notes/09-observation-and-modal-affordances.md)
- [10 · Relation-first dynamics, allegories, Kleisli categories, and effects](notes/10-relations-allegories-and-effects.md)
- [11 · Feedback is an operation with its own existence and coherence obligations](notes/11-feedback-and-trace.md)
- [12 · Local-to-global behavior: presheaves, sheaves, and stacks](notes/12-sheaves-and-stacks.md)
- [13 · Events and causal structure instead of one global state clock](notes/13-events-concurrency-causality.md)
- [14 · Diffeological and Frölicher spaces: smoothness without manifold charts](notes/14-diffeology-and-frolicher.md)
- [15 · Weil functors, jets, Cartan distributions, and the variational bicomplex](notes/15-weil-jets-and-pde-geometry.md)
- [16 · Dirac structures and Tulczyjew triples: constraints, energy, and dynamics](notes/16-dirac-and-implicit-physical-systems.md)
- [17 · Groupoids, stacks, and derived solution spaces: do not erase witnesses too early](notes/17-gauge-and-derived-solution-spaces.md)
- [18 · Lenses, open games, and interaction semantics](notes/18-lenses-games-and-interactions.md)
- [19 · Exceptions and replanning: distinguish the event, the judgment, and the obstruction](notes/19-exceptions-and-replanning.md)
- [20 · A typed architecture for heterogeneous open components](notes/20-architecture-and-proof-obligations.md)
- [21 · Worked finite example: what survives the boundary?](notes/21-small-worked-example.md)
- [22 · Discriminating probes and unresolved research questions](notes/22-probes-and-unresolved-questions.md)
- [23 · Other decomposition techniques in reserve](notes/23-other-techniques-in-reserve.md)
<!-- END MANIFEST -->

## Three warnings that should survive future compression

1. An internal category of executable partial transitions and a category of **open components** are generally different levels; an internal restriction idempotent does not automatically determine an observable boundary restriction.
2. A categorical operation can guarantee correct *composition* of meanings without furnishing a feasibility decision algorithm, solver, controller, or optimal policy.
3. Any claim of minimal, universal, or “freely varying” system factorization is conditional on declared interfaces and the questions that need to remain answerable after assembly.

The notebook also includes a [finite verification record](CHECKS.md). It complements—but does not supersede—the earlier, more forensic 40-claim audit, included as a separate appendix in the ZIP. This main notebook is intended to be reusable as individual knowledge notes.
