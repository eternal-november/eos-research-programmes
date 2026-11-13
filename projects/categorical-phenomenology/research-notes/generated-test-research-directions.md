# Research directions after `generated_characterizations_note.tex`

> Status: Exploratory research directions and candidate arguments, not an accepted programme amendment or a proof-assistant certificate. Claims of established results refer to the underlying manuscripts; proposed extensions remain proposals.

The newest results open several worthwhile directions. The strongest are not necessarily larger generalizations; some concern unresolved compatibility conditions within the mathematics already developed.

The immediate research situation is:

- Established: Exact criteria for preserving FCA closure, predictive-state equivalence, and Dowker complexes when adding tests.
- Established: A largest extensional completion preserving those three structures simultaneously.
- Established: Future-test generation, action-compatibility conditions, Boolean-saturation results, and homotopy criteria for adjoining tests.
- Unresolved: How these constructions behave under uncertain evidence, changes of observational domain, alternative preservation requirements, and simultaneous structural and dynamical refinement.

The original program also concerns the formation of mathematical and scientific structures, not only the preservation of existing ones. That broader objective remains distinct from the technical questions below.

## 1. A decisive obstruction to organize the next research

Consider

\\[ H=\\{0,1\\}, \qquad \mathcal E=\\{\\{0\\},\\{1\\}\\}. \\]

The associated object Dowker complex has two isolated vertices, hence homotopy type \\(S^0\\).

Now generate the disjunction of the two predicates. Its extent is \\(H\\). Adding it as a test produces a full edge, which is contractible.

Yet the observational distinctions have not changed. The FCA closure is also unchanged.

Therefore:

\\[ \boxed{ \text{Logical definability} \not\Rightarrow \text{topological conservativity}. } \\]

This establishes an important design obstruction. A framework cannot simultaneously require that arbitrary logically defined tests leave the reconstructed topology invariant and that every test be treated as an additional Dowker witness.

One requirement must be weakened, or the interface must distinguish logically available predicates from predicates admitted as geometric or observational witnesses.

That is a natural starting point for several independent investigations.

## 2. Nine worthwhile directions

| Direction                                    | Research question                                                                                                                    | Decisive result                                                                | Type         |
| -------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------ | ------------ |
| A. Joint homotopy conservativity             | When can several individually harmless generated tests be added together without changing topology?                                  | A compatibility theorem, classification of admissible families, or obstruction | Probe        |
| B. Semantic roles of tests                   | How should derived formulas, executable measurements, and designated topological witnesses be distinguished?                         | A compositional interface invariant under appropriate definitional extensions  | Design       |
| C. Incomplete-evidence preservation          | Which generated tests are conservative in every world compatible with the observations?                                              | Sound certificates and counterexamples under partial evidence                  | Design       |
| D. Equivariant homotopy preservation         | When does topological equivalence survive the dynamics and exact partial-action domains?                                             | An action-compatible comparison theorem or obstruction                         | Probe        |
| E. Robust topological reconstruction         | Can test generation preserve stable, noise-tolerant topology instead of exact Boolean topology?                                      | A quantitative interleaving or persistence-preservation theorem                | Probe        |
| F. Probabilistic characterization generation | What replaces Boolean future-test closure for stochastic systems?                                                                    | A construction respecting probability laws and Markov lumpability              | Design/probe |
| G. Cross-context naturality                  | How do conservative completions transport when the state domain, available tests, or actions change?                                 | Naturality laws with explicit failure conditions                               | Probe        |
| H. Certified finite algorithms               | Can the preservation checks produce machine-checkable certificates without enumerating every concept or simplex?                     | A verified implementation with complexity bounds                               | Solve/design |
| I. Cross-domain emergence                    | Which parts of this construction survive in mathematical theory formation, scientific modeling, and other reconstruction mechanisms? | A substantive comparison theorem across different native structures            | Probe        |

The first four are particularly close to the mathematics already developed. They do not require an automatic scientific-law discovery procedure.

## 3. A particularly promising obstruction: individually safe tests may be jointly unsafe

The latest note characterizes adding one test and gives sufficient conditions for adding sequences of tests. A related issue deserves separate investigation.

Take a complex \\(K\\) consisting of the boundary of a square:

\\[ K:\quad 1-2-3-4-1. \\]

It has homotopy type \\(S^1\\).

Now consider two new test extents:

\\[ D_1=\\{1,2,3\\},\qquad D_2=\\{1,3,4\\}. \\]

Original: one loop

Adding \\(D_1\\): loop survives

Adding \\(D_2\\): loop survives

Adding both: filled disk

Each test separately attaches a triangle along a contractible path. Consequently, either single addition preserves the homotopy type of \\(K\\).

But together the triangles fill the square, making the result contractible.

This gives a sharp conclusion:

Unlike literal three-structure preservation, homotopy-conservative test addition is not generally closed under taking unions of admissible test families.

In particular, there need not be a unique largest homotopy-conservative completion containing the original test family.

That changes the mathematical problem. Instead of a largest safe completion, the appropriate objects may be maximal compatible families, conflict certificates, or admissible generation schedules.

An immediate research question is:

> Can the interactions among homotopy-conservative test additions be characterized by finite obstruction families? Under what conditions does local compatibility imply global compatibility, and what changes when tests must also respect sequential actions?

This is probably the strongest narrowly mathematical continuation.

## 4. A more foundational direction: separate definability from observation

The existing framework treats a generated test as an additional column when it is admitted to the incidence relation.

But three operations are materially different.

Deriving a formula establishes a logical expression and its meaning.

Executing an experiment establishes an observation with a specified procedure, cost, and uncertainty.

Designating a predicate as a topological witness changes which common incidences define simplices.

A theory could represent all three without identifying them.

The desired result would be a compositional semantic interface in which a definitional extension preserves the underlying measured data and designated topology unless a separate, authorized operation changes the witness family.

An important falsifier is the two-object disjunction example. Any proposed interface that automatically turns the disjunction into a new geometric witness will fail to preserve the old topology.

This direction is more about the architecture of mathematical representation than about discovering a new scientific law. Its payoff would be avoiding artificial topology changes caused solely by enlarging logical syntax.

## 5. Incomplete evidence and robust guarantees

The existing preservation results assume an exact relation on a declared domain.

A natural next problem is to replace that assumption with a set \\(W\\) of admissible completions of the available evidence.

For a candidate generated formula \\(\varphi\\), define the preservation requirement

\\[ \forall w\in W,\qquad \llbracket\varphi\rrbracket_w \in\operatorname{Safe}(\mathcal E_w). \\]

This is the right logical shape for a guarantee that holds despite unresolved observations.

The main research obligation is not merely writing that quantifier. It is determining how to verify it efficiently while preserving correlations among unknown entries.

One could ask whether the preservation conditions admit sound SAT/SMT certificates, compositional rules for generated formulas, and minimal counterexample completions.

Incomplete FCA contexts and logical preservation already have substantial literatures, so novelty would have to lie in the joint structural requirements rather than in handling unknown Boolean entries alone.&#x20;





## 6. Dynamics and topology together

The newest note proves homotopy-preservation results and, separately, preservation laws for actions on incidence structures.

The next issue is whether these can be combined under weaker conditions than literal equality of the complexes.

Suppose a test extension induces a homotopy equivalence

\\[ K\hookrightarrow K^+. \\]

Must the action domains also be homotopy equivalent? No such implication follows merely from the equivalence of the full spaces.

A new theorem would need to compare the entire family of partial-action domains, their inclusions, and the maps induced by successive actions.

The decisive question is:

> What additional conditions ensure that a homotopy-conservative observation-language extension is also conservative for the partial dynamical system carried by the reconstructed topology?

A useful result would specify exactly which diagrams commute strictly, which commute only up to homotopy, and whether that compatibility survives composition of actions.

This is a direct continuation of `common_generation_note.tex`.

## 7. Robust topology rather than exact topology

The one-bit instability counterexample shows that ordinary Boolean Dowker homology is not uniformly stable under small normalized Hamming perturbations.

That suggests replacing exact incidence with an appropriately weighted or filtered relation.

However, the replacement must preserve the intended meaning of the tests. Assigning arbitrary numerical weights to a Boolean relation would not solve the underlying interpretation problem.

The research target should instead be a verified relationship between observation uncertainty and a filtration parameter, yielding an interleaving or persistence bound.

Existing sparse and weighted Dowker constructions already provide relevant stability machinery.&#x20;





The potentially interesting additional result would concern stability under logically or operationally generated tests, including their action compatibility.

## 8. Stochastic systems

The deterministic theory uses inverse images of test extents under state transitions.

For a Markov kernel \\(P\\), the corresponding operation on real-valued observables is

\\[ (Pf)(x)=\int f(y)\\,P(x,dy). \\]

This suggests generating an observable algebra under probabilistic transition operators, rather than only under Boolean inverse images.

The critical distinction is between preserving complete output-process laws and constructing a genuinely Markovian quotient.

Those are different obligations, as the latest note's stochastic counterexample demonstrates.

A useful theorem would characterize a minimal observable algebra or partition satisfying both the required prediction semantics and the transition-closure conditions needed for a quotient Markov process.

Probabilistic modal logics and abstract-interpretation approaches already provide much of the general background.&#x20;





## 9. A lower-risk implementation direction

`GeneratedTests.lean` currently formalizes a subset of the exact incidence and attribute-extension results.

A useful next deliverable would be a finite certificate checker that accepts a Boolean incidence table, an action presentation, and proposed generated tests.

It should output either a proof of the requested preservation property or a concrete witness of failure.

A stronger implementation would retain the chosen preservation criteria in the output type, so a certificate for residual-equivalence preservation cannot be mistaken for one establishing FCA or topological preservation.

This work is unlikely to supply a new mathematical principle, but it would make the existing theory more auditable and expose whether the proposed interfaces are computationally manageable.

## 10. Which directions have the greatest leverage?

| Research objective                                | Strongest direction                           | Main risk                                                                                       |
| ------------------------------------------------- | --------------------------------------------- | ----------------------------------------------------------------------------------------------- |
| Produce a new precise theorem                     | Joint homotopy conservativity                 | The classification may be combinatorially difficult or reduce to established attachment theory  |
| Improve the framework's conceptual foundations    | Semantic roles of tests                       | Creating a good interface without obtaining substantive consequences                            |
| Handle realistic incomplete observations          | Evidence-relative conservativity              | Computational complexity and correlated uncertainty                                             |
| Extend the existing common reconstruction theorem | Equivariant homotopy preservation             | Compatibility may fail except under strong extra conditions                                     |
| Obtain quantitative reliability                   | Stable generated-test topology                | Stability may require changing the observable or restricting the test grammar                   |
| Extend beyond deterministic Boolean systems       | Probabilistic observable closure              | Existing probabilistic modal logic and bisimulation theory may subsume most of the construction |
| Strengthen auditability                           | Verified finite checker                       | Implementation progress without mathematical novelty                                            |
| Advance the full phenomenology program            | Cross-domain structure-generation comparisons | Prematurely imposing one framework on genuinely different reconstruction mechanisms             |

The first direction has an unusually clear advantage: the example above establishes that a seemingly natural extension of the current largest-completion result is impossible. A subsequent theory must retain compatibility information between test additions.

The second addresses a deeper issue: what it means for a characterization to become available without automatically becoming a new observation or changing the invariant being reconstructed.

Both are independent of the automatic representation-language selection question, which can remain deferred.

## Recommended research fork

Two questions stand out.

Mathematical route:

> Characterize maximal jointly homotopy-conservative families of generated tests. Determine when individual preservation certificates compose, when they conflict, and whether compatible sequential actions impose additional obstructions. Seek sharp theorems and minimal counterexamples.

Foundational route:

> Construct a typed theory distinguishing logical derivation, executable observation, and designated structural witnesses. Determine which characterization extensions preserve semantics, observational quotients, concept lattices, and topology, and identify which preservation properties require explicit additional choices.

The mathematical route has the clearer immediate theorem target. The foundational route has broader relevance to the original phenomenology objective.

Neither requires claiming that the framework has already explained how scientific theories are invented. They investigate two more specific obligations exposed by the newest results.