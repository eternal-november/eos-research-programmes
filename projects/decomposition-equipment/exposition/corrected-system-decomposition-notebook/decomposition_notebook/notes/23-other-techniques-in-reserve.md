# 23 — Other decomposition techniques in reserve

**Origin:** chat L665–693 and L918–946. **Status:** corrected short concept notes. These were mentioned but not developed far enough in the source to justify a detailed application claim.

These are retained because an eventual downstream problem may reveal their relevance. Their absence from the main architecture is **not** a proof of irrelevance.

| Technique | Formal cut worth retaining | Important limitation / discriminant |
|---|---|---|
| **Inverse/restriction inverse categories** | Partial arrows equipped with suitable partial inverses; categorical abstraction of partial isomorphisms. | A dynamical system that admits backward *solutions* need not be modeled by partial inverses if distinct states merge, stochasticity is present, or history is lost. |
| **Markov categories** | Symmetric monoidal categories with copy/discard structure for stochastic processes. | A conditional distribution or disintegration need not exist for arbitrary measure spaces. “Markov category” alone does not solve filtering or causal identification. |
| **Comonads and context-dependent updates** | Coeffects/local context may be expressed through comonadic structure; useful in cellular/context-sensitive settings. | A comonad is not generally an environment-dynamics operator action and does not supply a particular local-update law. |
| **Chu spaces** | Pair points/observations with an evaluation relation or pairing, often \((A,X,\langle-,-\rangle)\). | Structural point/test duality does not guarantee experiments distinguish physical states or provide a controller. |
| **Synthetic differential geometry** | Infinitesimal objects and internally formulated differentiation in a chosen smooth topos or related model. | Requires an ambient logic/model with appropriate infinitesimal axioms; not interchangeable with ordinary manifolds or an ODE solver. |
| **Cohesive toposes** | Adjoints/modalities separating shape, discrete, and codiscrete aspects of space in a cohesive setting. | “Cohesion” is not a generic physical coupling law or a flow semantics. |
| **Lie groupoids/algebroids** | Global symmetry/groupoid data versus infinitesimal anchored-bracket data. | A Lie algebroid need not integrate to an ordinary globally well-behaved groupoid; the integration and quotient questions are separate. |
| **Equipments/framed bicategories** | Distinguished vertical maps and horizontal proarrows with companion/conjoint-type structure where axioms hold. | Not every double category is an equipment; interface refinement versus behavior arrows requires a deliberate semantic assignment. |
| **Polycategories / linearly distributive categories** | Multiple-input/multiple-output composition with designated cut operations. | A symmetric monoidal category already has multi-port objects; extra polycategorical structure is justified only when the richer multicut behavior is actually consumed. |
| **Quantaloid enrichment** | Typed weighted relations with ordered-compositional semantics. | Requires specified hom-orders and composition; “reachability + cost + probability” is not one automatic enriched structure. |
| **Causal sites** | Two interacting region relations, e.g. containment and causal precedence. | Do not identify with event structures or claim causal order alone generates propagation laws. |
| **Hypergraph categories** | String-diagram wiring with special commutative Frobenius structure on objects. | A junction is not automatically physical equality, nondestructive copying, conservation, or a safe signal fan-out; semantics must be chosen. |

## Decision policy

Promote one of these candidates from reserve only after naming its **consumer** (a question, invariant, verification obligation, or assembly operator), its **additional preserved distinction**, and a **witness that a simpler model cannot answer the same question faithfully**. Otherwise it is a concept available for later search, not a proposed default framework.

**Related notes:** [03](03-types-of-physical-law.md), [07](07-wiring-and-open-systems.md), [10](10-relations-allegories-and-effects.md), [22](22-probes-and-unresolved-questions.md).
