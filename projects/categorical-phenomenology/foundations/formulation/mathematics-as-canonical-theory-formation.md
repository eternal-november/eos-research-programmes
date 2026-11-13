---
status: >
  Developing research programme. Relative canonicity and the cyclic-group nonidentification witness are supported by direct arguments, checked in a first pass. General theory formation and the philosophical interpretation remain open; no claim of repository acceptance is made.
---

# Mathematical theory formation and relative canonicity

Mathematical theory formation can turn observations, existing results, and intended uses into explicit structural obligations, then construct concepts, operations, and inferential systems that satisfy them. The generative ambition is to obtain mathematical structure through this process, including structure not supplied in the initial presentation. A category of already available theories is useful for comparison, but does not by itself achieve that ambition.

Canonicity is one possible achievement within this programme. Once the input, admissible constructions, and comparison maps have been specified, a universal property can characterize a construction uniquely up to the appropriate equivalence. Whether those specifications are warranted by the observations, and whether the observations identify the constructed object, are separate questions.

The proposal therefore combines constraint with revision. A mathematical problem can sharply constrain the available constructions without determining every choice. Once axioms and inferential rules are fixed, their derivable consequences are fixed; discovering those consequences may expose a defect in the original formulation or suggest new constructions. Choices about primitives, equality, proof identity, admissible inference, and idealization can change mathematical content. Their responsiveness to a problem does not make them merely changes of coordinates.

## From observations to generative structure

An observation regime specifies what can be presented, which comparisons or interventions are available, and what responses count as evidence. Its objects need not be physical: a proved obstruction, a recurring construction, a failed preservation claim, or an unexpected correspondence within existing mathematics can supply a substantive starting point. The kind of support still matters. A proof, a computed sample, an experimental measurement, and an interpretation do not become interchangeable by being called observations.

A phenomenon, in this programme, is an articulated regularity, dependence, or obstruction that a candidate theory is expected to account for. It may be represented by a proposition, a response relation, an invariant, or another structure appropriate to the task. Its intermediate role between records and theories does not establish a new ontological kind that is neither data nor proposition. Neither does it make every phenomenon an already formed fragment of a theory: the operations needed to compose it with other phenomena may still be unknown.

Stabilization turns some of these patterns into exact structural requirements. It can introduce idealizations, specify which distinctions may be identified, or demand operations extending beyond the observed instances. Those commitments need their own warrants. An observed regularity, a requirement imposed by an intended use, and a convenient hypothesis can all constrain a construction, but they supply different reasons for accepting it.

A schematic account of the work is

\[
\text{evidence and intended uses}
\longrightarrow
\text{articulated constraints}
\longrightarrow
\text{candidate constructions and consequences}.
\]

These arrows denote tasks, not established functors or a universal chronology. Consequences feed back into the evidence and the formulation: they can suggest a distinguishing observation, reveal incompatible constraints, or make a different vocabulary useful. Both the observational interface and the structural doctrine may change.

The [two-sided realization proposal](towards-two-sided-context-sensitive-factorization-based-realization.md) supplies an exact setting for part of this work: construct admissible factorizations of specified interactions and prove that they preserve the required contexts. It also distinguishes that construction from inferring complete behavior from partial evidence and from discovering the vocabulary in which the behavior is expressed.

## What can be determined

The word “theory” can refer to an axiom system, its deductive closure, a class of models, or a mathematical object equipped with a universal property. The following claims concern different objects and have different warrants.

| Claim | Required setting and warrant |
|---|---|
| The consequences are determined | Fix a language, axioms, and consequence relation. Their deductive closure is then fixed. This does not imply completeness, decidability, or an effective method for discovering every consequence. |
| A construction is canonical | Fix the input, ambient category, comparison maps, and universal property; establish existence. The universal property supplies the corresponding uniqueness, such as unique isomorphism respecting the structure maps. |
| The evidence identifies a structure or consequence | Establish a nonempty class of admissible realizations fitting the evidence. All must agree on the target modulo the specified equivalence; agreement only within a tolerance gives a weaker, bounded-ambiguity claim. |

A free construction can be canonical without identifying an unknown source. Conversely, a useful consequence can be identified even when the entire realization is not. The [identification and descent note](of-learning/identification-and-descent-in-contextual-realization.md#3-target-identification-versus-a-canonical-realization) gives the exact set-level criterion for a target to factor through an observation map. It also keeps identification separate from stable recovery and computability.

Universal properties do not establish their own existence or empirical relevance. Nor does characterizing a selected object by a specially tailored property explain why that property answers the original problem. The property must express an independently justified construction or preservation obligation.

### A canonical construction with unidentified realizations

Suppose the structural doctrine is groups with a designated generator \(g\). For a fixed integer \(N\geq1\), the observations test all equalities

\[
g^i=g^j,\qquad -N\leq i,j\leq N,
\]

and report equality exactly when \(i=j\). This example assumes exact equality tests and the group doctrine; it omits noisy observation and discovery of the group operations. Its purpose is to separate canonical generation from identification even after those choices are fixed.

Let \(\mathcal R_N\) have cyclic groups with designated generator satisfying these observations as objects, and generator-preserving group homomorphisms as arrows. Both \((\mathbb Z,1)\) and \((\mathbb Z/m\mathbb Z,\overline1)\), for every \(m>2N\), are objects. Indeed, in the tested range,

\[
|i-j|\leq2N<m,
\]

so \(m\) divides \(i-j\) exactly when \(i=j\). The finite and infinite cyclic groups therefore reproduce precisely the same observations, although they are not isomorphic.

There is nevertheless a canonical generated object: \((\mathbb Z,1)\) is initial in \(\mathcal R_N\). For each \((G,g)\), the map

\[
f:\mathbb Z\to G,\qquad f(n)=g^n
\]

is a homomorphism sending \(1\) to \(g\), and every such homomorphism must have this form. This proves the required existence and uniqueness of the comparison map. The construction gives formal powers, their composition, and inverses from one generator. These maps preserve the observed responses but may identify untested powers; requiring reflection of all power equalities would change the comparison doctrine.

Yet \(g^m=e\) holds in the finite cyclic candidate and fails in the infinite one. Observations and structural doctrine have stayed fixed while a material claim remains unidentified. Extending the tests to that equality separates these two candidates. If “the theory” instead means only the deductive consequences common to the admitted laws and observations, this claim remains undecided.

The example supports a substantive role for universal construction: it produces a reusable mathematical object and comparison maps. It also shows why canonicity cannot be used as evidence that the object is the uniquely correct reconstruction of an observed source. Alternative realizations need not arise from changing the problem.

## The non-vacuity constraint

The claim that all mathematical knowledge originates in observation of something is a separate philosophical thesis. Allowing “observation of mathematics itself” makes it possible to redescribe almost any activity in observational language; that redescription alone explains little. Large cardinals, surreal numbers, or higher categorical constructions are not accounted for merely by placing them under this clause. Each proposed account needs an actual dependence between its motivating material, its construction choices, and what it produces.

The operative requirement is discriminating content. Specify what the evidence constrains, what the construction adds, which alternatives remain possible, and which consequences or uses can distinguish them. Naming an observation category is helpful only insofar as its objects, maps, and laws preserve those distinctions. A formally typed interface can still be vacuous as an explanation of theory formation.

The [corrected judged-argument example](example-synthesizing-fol-from-judged-arguments.md) exhibits this issue concretely. The supplied labels fit a first-order candidate, but also fit alternative interpretations that lack some standard connective rules. Constructing the candidate under explicit rules gives a mathematical result; it does not establish that the labels forced those rules. Additional judgments can discriminate among the displayed alternatives, while selection of an entire doctrine remains a further obligation.

This keeps internally generated phenomena useful without making the account circular. Constructing an object and proving an unexpected property can create a new constraint for subsequent work. It does not retrospectively show that the original choice of object was forced.

## Distinguishing reconstruction operations

Quotienting, generation, completion, and deductive closure perform different work. A response-profile quotient identifies distinctions unavailable to the specified tests. A free construction generates composites under chosen laws. A completion supplies objects required by a selected closure condition. Deductive closure records consequences under specified rules. They may compose, but their compatibility and their relation to the original observations need to be established.

The cyclic-group construction generates indefinitely many powers from one generator. Its short description is useful, but its universal property is a statement about homomorphisms, not a description-length theorem. Calling every theory a “universal compression” obscures this distinction. Compression requires a specified representation, cost, and preserved information; canonical completion alone supplies none of those measures.

Likewise, stable sections, invariants, and observational equivalence classes are not interchangeable definitions of phenomenon. The appropriate construction depends on whether the task concerns local compatibility, a preserved quantity, indistinguishability, or another requirement. Gluing also requires actual compatibility data and an assembly result. Locally adequate fragments need not form a globally adequate theory.

The choice of inferential rules can be substantive. For instance, permitting assumptions to be discarded licenses weakening; a calculus withholding that rule can distinguish judgments that the structural calculus identifies. Such a change is not automatically a new presentation of the same mathematical content. Equivalence of presentations must be established for the operations and judgments being preserved.

## Mathematical necessity and empirical applicability

Spatial experience can motivate geometric notions and requirements. It does not make a theorem of Euclidean geometry and the claim that a physical region is Euclidean the same kind of conclusion. The former follows from mathematical assumptions; the latter requires an interpretation connecting those assumptions to observation, including the relevant scale and tolerance. Exact idealizations must not inherit the evidential status of the measurements that motivated them.

Riemann's foundational lecture provides a useful precedent: it develops possible metric structures and separately asks how far their assumptions are borne out by experience and can be extended beyond the observed range. This supports a relation between mathematical construction and empirical inquiry without identifying their warrants. [✓] Bernhard Riemann, [On the Hypotheses which lie at the Bases of Geometry](https://www.maths.tcd.ie/pub/HistMath/People/Riemann/Geom/WKCGeom.html), Plan of the Investigation and III §§2–3, checked 2026-11-02.

The same separation matters for internal mathematics. Theorems can be necessary relative to fixed assumptions while the choice of assumptions remains revisable. A construction's usefulness can motivate studying it without proving that it is uniquely compelled by its motivating problem.

This programme concerns the construction, justification, and use of mathematical theories. It does not settle the discovered-versus-invented opposition or rank Platonism, formalism, conventionalism, and empiricism. Constraints can make choices highly nonarbitrary without making them merely notational. Dependence of knowledge on an access process does not entail dependence of mathematical objects or truth on that process. Nor does plurality of formal frameworks alone force access-relative truth. Those philosophical interpretations require arguments beyond the reconstruction results.

## Research programme

The generative target has two levels. Within a specified doctrine, construct a realization from observational or mathematical constraints and show what it preserves. Beyond a fixed doctrine, develop or revise the vocabulary, operations, inference rules, and admissible comparisons themselves. Success at the first level supplies examples and constraints for the second, but does not automatically solve it. A general programme should retain both levels rather than reduce theory formation to fitting parameters or organizing existing theories.

The useful exact cases should produce objects, proof systems, models, or comparison maps that were not supplied as the answer. Their justification must connect the output to the original constraints and required contexts. The cyclic-group construction supplies one limited witness; the first-order example supplies a candidate calculus whose identification remains open. The two-sided realization framework provides further constructions and preservation obstructions. Where several admissible realizations remain, the programme can still determine which consequences they share and what additional evidence would distinguish them.

Categorical machinery is warranted by these construction and transport obligations. A fibration requires specified reindexing and coherence, not merely a family indexed by contexts. A functorial learning account requires identified objects, updates or comparisons, and composition laws. Learning may change predicted behavior, so its updates need not preserve one fixed observation table. Sections, quotients, Kan extensions, and descent are available constructions under their respective hypotheses, not compulsory stages of a single pipeline.

There are scoped precedents. *Backprop as Functor* constructs a category of learning updates and a monoidal functor from parametrized functions under stated assumptions on gradient descent and the error function. It supplies compositional structure for a particular learning regime. [✓, stated result scope] Fong, Spivak, and Tuyéras, [Backprop as Functor](https://arxiv.org/abs/1711.10455), checked 2026-11-02. Effectus theory supplies categorical structure for states, predicates, and quantitative logic, including classical and probabilistic cases. It is a substantive candidate regime, not a general procedure deriving arbitrary mathematical theories from observations. [✓, stated scope] Cho, Jacobs, Westerbaan, and Westerbaan, [An Introduction to Effectus Theory](https://arxiv.org/abs/1512.05813), checked 2026-11-02.

The [learning strand](of-learning/todo.txt) retains possible developments of these connections. Their common form and their limits have to be exhibited; sharing a diagrammatic shape does not prove that supervised learning, scientific theory revision, and mathematical abstraction are the same process.

The guiding proposal is to construct mathematical structure that answers to explicit phenomena and intended uses, then use its consequences to refine both the evidence and the problem. Relative canonicity is valuable when its universal property expresses that obligation. Unresolved choices remain part of the mathematical problem rather than evidence that the programme has failed.
