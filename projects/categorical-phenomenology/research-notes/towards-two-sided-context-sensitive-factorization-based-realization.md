## Finding

**The strongest candidate is a theory of two-sided testing and realization: categories of context-compatible factorizations of observable interactions, with comparison maps justified by preservation theorems.**

The most useful existing mathematical core is **factorization-based realization**, including **cylinder factorization systems and their connection to Isbell envelopes**. The closest existing model for *organizing different approaches* is Andrew Stacey’s **Comparative Smootheology**. Neither supplies a complete theory of phenomenology, but together they provide substantially more than a sufficiently large category in which everything can be placed. [arXiv](https://arxiv.org/abs/1410.7108)

This recommendation uses a specific criterion: an organizing structure should help **construct something from observations, determine which operations it supports, and explain why a comparison succeeds or fails**. Mere coverage of the attached landscape is not enough.

The evidence is strongest for exact behavioral reconstruction, test-defined mathematical structures, and changes of representation. It is weaker for finite noisy evidence, discovery of the test vocabulary, and reconstruction of explanatory decomposition. Those are limitations of the recommendation, not problems already solved by the proposed terminology.

Importantly, the recommendation is **not** “everything is an Isbell nucleus,” “everything is a factorization,” or “put all theories in a double category.” The organizing object should retain different reconstruction operations and their admissibility conditions. The attachment already correctly distinguishes a nucleus construction from an image factorization; that distinction survives the analysis below. categorical-phenomenology-metho…

## 1. The organizing datum should be an interaction—not an already reconstructed object

Start with a testing correlation

\[
H:P\times T\longrightarrow\Omega,
\]

where \(P\) consists of preparations, histories, or presented situations; \(T\) consists of tests or continuations; and \(\Omega\) records responses.

This notation does not require responses to be deterministic scalar measurements. A response could retain a probability distribution, compatibility relation, or witness space. The choice matters: replacing a distribution with its mean is already an information-losing transformation, not an innocent change of notation.

A realization introduces an intermediate object \(S\):

\[
H(p,t)=\operatorname{ev}(r(p),t),
\qquad
r:P\to S.
\]

But this bare equation is insufficient. Almost any table can be encoded in an object called \(S\). The substantive question is:

> **Through which admissible kinds of object can the interaction factor, while preserving the required contexts and operations?**

A set, vector space, stochastic latent state space, smooth space, concept lattice, and compositional dynamical system impose different requirements.

The two-sided formulation generalizes from individual preparations and tests to diagrams of preparation objects \(D_i\) and measurement objects \(E_j\), with a compatible family of observable maps

\[
\rho_{ij}:D_i\longrightarrow E_j.
\]

A realization is a factorization

\[
D_i\xrightarrow{p_i}S\xrightarrow{q_j}E_j,
\qquad
q_jp_i=\rho_{ij}.
\]

This is the shape of a **cylinder factorization**: a family of interactions factors through a shared intermediate object. In a cylinder factorization system, designated classes of cocones and cones satisfy an orthogonality condition that makes the designated factorization essentially unique. Garner’s *The Isbell Monad* characterizes such systems as pseudoalgebras for the Isbell-envelope pseudomonad. This is an established connection between two-sided observational presentations and factorization—not an analogy invented for this discussion. [arXiv](https://arxiv.org/abs/1410.7108)

However, an arbitrary cylinder factorization system does not automatically mean “empirically justified reconstruction.” The designated classes must acquire that meaning in the application.

### Two elementary instances show the value of the formulation

**In sets**, a response table gives the row-profile map

\[
P\longrightarrow\Omega^T,
\qquad
p\longmapsto H(p,-).
\]

Its surjection–injection factorization produces

\[
S_H=\{H(p,-):p\in P\}.
\]

Thus preparations are identified exactly when the specified tests give identical responses. This is a reconstruction of **observational states**, relative to those tests.

**Over a field \(k\)**, a numerical table gives a linear map

\[
k^{(P)}\longrightarrow k^T,
\qquad
e_p\longmapsto H(p,-).
\]

Its image is the span of the response profiles. For a finite table, its dimension is the matrix rank.

The observations can therefore support a set-based realization or a linear realization without identifying the two. The former retains distinct rows; the latter additionally permits linear combinations. That additional structure comes from the chosen realization doctrine, not from the word “observation.”

### Context compatibility is part of the datum

Suppose an admissible operation \(c\) on preparations induces an operation \(c^\ast\) on tests satisfying

\[
H(cp,t)=H(p,c^\ast t).
\]

Then equality of complete test profiles is preserved by \(c\). Consequently, \(c\) descends to the observational quotient.

Without such a compatibility law, a quotient can preserve present measurements while destroying future predictions or composition. This is why the proposed center is **context-compatible realization**, not merely factorization of a static table.

For open systems, the relevant contexts may include wiring, boundary attachment, control interventions, and—in regimes where it is defined—feedback. Their admissibility cannot be inferred from a generic factorization theorem.

## 2. The strongest comparative precedent is *Comparative Smootheology*

Stacey’s paper is unusually close to the actual organizing problem.

It compares several notions of generalized smooth space by presenting structures through **test objects, maps into and out of an underlying object, and forcing conditions**—conditions determining which test maps must be admitted. Comparisons arise by changing the test category, underlying category, or forcing conditions. The paper constructs functors, investigates adjunctions and embeddings, and proves non-equivalence results. Its comparisons are initially constrained to preserve the shared smooth-manifold fragment. [arXiv](https://arxiv.org/abs/0802.2225)

That last feature is important: the translations are constrained by independently understood mathematics, rather than chosen solely to make a square commute.

The limitation is equally important. This is primarily a theory of **test-defined structures on underlying objects**, not an algorithm for discovering unknown physical state spaces from finite experimental records.

Nevertheless, it supplies a successful comparative pattern:

\[
\text{change tests or structural requirements}
\quad\Longrightarrow\quad
\text{construct comparison functors}
\quad\Longrightarrow\quad
\text{prove preservation or obstruction}.
\]

That is a much stronger precedent for an organizing structure than the mere possibility of making a category of approaches.

There is also independent evidence beyond generalized smooth spaces. Pavlovic and Fauser’s *Smooth Coalgebra: Testing Vector Analysis* reconstructs tangent and cotangent structures through a testing correlation between paths and real-valued functions. At a point, the relevant pairing is essentially

\[
(\gamma,f)\longmapsto
\frac{d}{dt}(f\circ\gamma)(0).
\]

The construction presupposes the smooth setting; it does not discover smoothness from raw data. But it demonstrates that testing-based reconstruction has mathematical applications outside automata and statistical inference. [arXiv](https://arxiv.org/pdf/1402.4414)

## 3. The strongest generative core is realization by extension and factorization

There is a more concrete construction than an unrestricted category of candidate models.

Let

\[
i:\mathcal O\hookrightarrow\mathcal I
\]

be a fully faithful inclusion. Here \(\mathcal O\) describes observable interactions, while \(\mathcal I\) additionally describes the internal operations a realization must support. An observable behavior is a functor

\[
D:\mathcal O\to\mathcal V.
\]

A realization extends it to

\[
X:\mathcal I\to\mathcal V,
\qquad
Xi\cong D.
\]

Where the relevant Kan extensions exist, they give initial and terminal realizations:

\[
\operatorname{Lan}_iD,
\qquad
\operatorname{Ran}_iD.
\]

With a suitable factorization system, the canonical map between them factors as

\[
\operatorname{Lan}_iD
\longrightarrow
M_D
\longrightarrow
\operatorname{Ran}_iD.
\]

Colcombet and Petrişan develop this construction for categorical automata minimization. The resulting object is obtained equivalently by taking the observable quotient of a reachable realization or the reachable part of an observable realization. Minimality is relative to the specified factorization system—not an unqualified claim about smallest parameter count. [Logical Methods in Computer Science](https://lmcs.episciences.org/6213/pdf)

This matters because **the internal state object is an output of the construction**. It is not simply a vector space selected beforehand and subsequently fitted.

There is algorithmic evidence as well. Barlocco, Kupke, and Rot’s *Coalgebra Learning via Duality* separates states from logical tests and generalizes active automata learning. Under its stated assumptions, termination returns a reachable model correct and minimal with respect to the chosen logical equivalence; termination itself requires an appropriate finite logical quotient. The procedure also relies on its specified teacher/query interface, not unrestricted passive data. [Springer Link](https://link.springer.com/chapter/10.1007/978-3-030-17127-8_4)

These are reasons to favor testing and realization as an organizing center: the framework has already produced constructions, algorithms, and correctness results.

## 4. A genuine comparison: concept completion versus behavioral realization

For a language \(L\subseteq\Sigma^\ast\), consider the prefix–suffix observation relation

\[
H_L(u,v)=1
\quad\Longleftrightarrow\quad
uv\in L.
\]

Clark’s work explicitly connects this relation both to Myhill–Nerode identification and to Galois-connection-based automaton constructions. His separate *syntactic concept lattice* uses two-sided contexts; those two relations should not be conflated. [Rational Empiricism](https://alexc17.github.io/static/pdfs/JLC2013.pdf)

The following comparison can be derived directly.

### Behavioral realization takes the image

The row belonging to \(u\) is the residual language

\[
r_u=u^{-1}L.
\]

The reachable minimal deterministic state set is

\[
Q_L=\{r_u:u\in\Sigma^\ast\}.
\]

Its transition on a letter \(a\) is

\[
r_u\longmapsto r_{ua}.
\]

### Concept formation takes a closure

The intents of the formal context are

\[
\mathcal I_L
=
\left\{
\bigcap_{u\in U}r_u:
U\subseteq\Sigma^\ast
\right\},
\]

including the empty intersection \(\Sigma^\ast\).

This is the intersection closure of the response rows, not merely their image. Ordered by inclusion, it is opposite to the usual concept-lattice ordering on intents.

There is a canonical inclusion

\[
Q_L\hookrightarrow\mathcal I_L.
\]

Moreover, left derivatives preserve intersections:

\[
a^{-1}\!\left(\bigcap_j S_j\right)
=
\bigcap_j a^{-1}S_j,
\]

and satisfy

\[
a^{-1}r_u=r_{ua}.
\]

Consequently, the derivative transitions extend to \(\mathcal I_L\). With initial state \(L\) and acceptance determined by membership of the empty word, **the residual automaton is precisely the reachable part of this completed deterministic automaton**.

This is an explicit relationship between two different observation-to-structure operations:

\[
\boxed{\text{row image}}
\qquad\text{and}\qquad
\boxed{\text{intersection completion}}.
\]

They are related, but they do not solve the same optimization problem.

For the unary language of even-length words, the residual states are the even and odd languages:

\[
Q_L=\{E,O\}.
\]

The intent structure has four elements:

\[
\mathcal I_L=\{\varnothing,E,O,\Sigma^\ast\}.
\]

The additional elements are justified by the chosen closure operation. They are **not forced as reachable states** by the language’s behavior.

That distinction is directly relevant to phenomenology: introducing a concept, ideal object, or completed type is not the same act as identifying an empirically necessary state.

## 5. A substantive obstruction: linear realization versus stochastic realization

The realization doctrine is not a decorative parameter. It can change what reconstruction is possible.

Consider the row-stochastic response table

\[
H=\frac12
\begin{pmatrix}
0&0&1&1\\
1&0&0&1\\
1&1&0&0\\
0&1&1&0
\end{pmatrix}.
\]

Each row is the outcome distribution of one preparation.

This is a rescaled and permuted version of a standard rank-versus-nonnegative-rank example discussed by Huh and Sturmfels. The distinction captures a real difference between linear representations and latent probabilistic models. [Princeton Math](https://web.math.princeton.edu/~huh/LikelihoodGeometry.pdf)

Here is a direct verification.

### Linear realization needs inner dimension three

The first and third rows sum to the second and fourth, so the rank is at most three. A nonzero \(3\times3\) minor establishes

\[
\operatorname{rank}_{\mathbb R}H=3.
\]

Thus \(H\) factors through a three-dimensional real vector space.

### A stochastic latent realization needs at least four states

A latent model with \(k\) states would factor

\[
H=AB,
\]

where \(A\) is a \(4\times k\) stochastic matrix and \(B\) is a \(k\times4\) stochastic matrix.

Each latent state contributes a nonnegative rank-one matrix. Its positive entries form a rectangle: a set of rows crossed with a set of columns.

The support of \(H\) has eight positive entries, no fully positive \(2\times2\) rectangle, and only two positive entries in each row or column. Therefore any positive rectangle contains at most two entries. At least four nonnegative rank-one summands are necessary.

Four suffice, using \(A=I_4\) and \(B=H\). Hence

\[
\operatorname{rank}_+(H)=4.
\]

**The three-dimensional linear realization cannot be lifted to a three-state stochastic realization.**

The obstruction is not insufficient data: the complete response table is given. Nor does it establish nonexistence of any stochastic realization: a four-state one exists. It obstructs a particular preservation claim—retaining the linear factorization width while imposing nonnegativity and stochastic admissibility.

This is exactly the sort of result an organizing theory should make visible. “Same observations” does not mean “same admissible latent structure,” and “minimal” cannot be transported between doctrines without a theorem.

## 6. Comparison squares should be consequences of preservation

A square becomes informative when its isomorphism is obtained from independently meaningful structure.

Suppose two realization settings have canonical objects \(M'_D\) and \(M_{dD}\), and a comparison

\[
F:\mathsf{Real}'(D)\longrightarrow\mathsf{Real}(dD).
\]

Here \(d\) changes the observational presentation and \(F\) translates realizations.

For factorization-based reconstruction, a sufficient condition is that \(F\) preserve the relevant initial and terminal realizations and the two factorization classes.

Then

\[
F(M'_D)\cong M_{dD}.
\]

The proof is short: applying \(F\) to the canonical source factorization produces a factorization of the target’s initial-to-terminal map. Essential uniqueness supplies the isomorphism.

For cylinder factorizations, the corresponding condition is preservation of the designated cocones and cones. This is precisely the kind of structure-preserving functor studied in the Isbell-monad account. [arXiv](https://arxiv.org/abs/1410.7108)

Thus the comparison square is not an extra axiom selected because it looks appropriate. It is a **derived exactness result**.

Under these hypotheses, coherence under composition follows from uniqueness of the comparison compatible with the factorizations. Without the preservation hypotheses, that argument is unavailable.

There are several materially different failures. A translation might preserve observed responses but fail to preserve the canonical realization. A realization might exist after translation but require a larger state space. A comparison might preserve an abstraction only approximately. Or an admissible realization might not exist at all.

These should remain different obstruction types.

### Keep the category of realizations when no canonical one is justified

For a fixed response diagram, retain admissible factorizations

\[
(D_i\xrightarrow{p_i}S\xrightarrow{q_j}E_j)_i{}_j.
\]

A morphism between two such realizations is an admissible map \(f:S\to S'\) satisfying

\[
fp_i=p_i',
\qquad
q_j'f=q_j.
\]

This records nonunique realizations and their actual comparisons. It does not force a quotient, closure, or preferred latent space.

A family of such categories over observational regimes is a reasonable organizing object. Calling it a **fibration** requires reindexing constructions and coherence proofs; that terminology should not be granted merely because the family is indexed.

Likewise, a partial order can be extracted after a specific reduction relation is established. It should not be the primary structure: passing immediately to reachability discards the maps and preservation witnesses that make the comparisons useful.

## 7. Why this is preferable to the strongest alternatives

The alternatives are not wrong. They have different centers of gravity.

| Candidate | What makes it substantive | Why it is not the preferred sole center |
|---|---|---|
| **Isbell nuclei and concept completion** | Canonical closure structures derived from two-sided interaction | Completion and reachable realization differ, as the language example demonstrates. |
| **Abstract interpretation** | Sound approximation, completeness, refinement, and preservation of computations | Strongest when the concrete semantics and required observations are already specified; the broader task also changes the admissible structure being reconstructed. |
| **Markov categories and statistical-experiment comparison** | Probabilistic composition, sufficiency, information orderings | These specify important observational and realization doctrines, but do not by themselves choose topology, algebraic structure, state decomposition, or admissible latent representation. |
| **A generic equipment or double category** | Retains objects, transformations, interactions, and comparison cells | Useful organizational infrastructure, but no reconstruction or preservation theorem follows merely from packaging the data this way. |
| **Two-sided testing plus admissible realization** | Starts at observational interaction; admits distinct reconstruction operations; supports exact comparison theorems and concrete obstructions | Requires additional theory for noise, locality, structural discovery, and some open-system compositions. |

Abstract interpretation deserves particular emphasis as the strongest nearby competitor, not an auxiliary afterthought. Amato and Scozzari prove existence of a least observationally complete abstract domain under continuity assumptions on state transitions; under additivity, their construction reduces to the complete shell. That is already a nontrivial answer to “which abstraction retains exactly the observations needed under computation?” [sci.unich.it](https://www.sci.unich.it/~amato/papers/wollic09.pdf)

The reason not to make abstract interpretation the entire organizing center is the broader scope of the task. The matrix example changes the allowed latent representations; the concept example changes the structural operation being demanded. A fixed lattice of abstractions does not automatically compare those choices. A common concrete domain might sometimes be constructed, but that construction—and its retained distinctions—would itself need justification.

Markov categories likewise supply genuine comparative results: categorical versions of statistical-experiment comparison and sufficiency are already developed. They belong inside the organization as mathematically substantial regimes, not merely as a probabilistic annotation. [arXiv](https://arxiv.org/abs/2010.07416)

## 8. Where this recommendation stops transporting

### Exact realization is not inference from finite data

The preceding constructions use a specified response relation or behavior. Actual evidence generally supplies a partial, noisy constraint on that behavior.

The distinction cannot be repaired by replacing equality with “approximately equal” without further choices. A metric, error model, confidence interpretation, and preservation bound are needed.

Even the matrix example exhibits the problem. Set

\[
H_\varepsilon=\frac{H+\varepsilon I}{1+\varepsilon}.
\]

These remain stochastic and converge to \(H\), but for every \(\varepsilon>0\),

\[
\det H_\varepsilon
=
\frac{\varepsilon(2\varepsilon^2-2\varepsilon+1)}
{2(1+\varepsilon)^3}>0.
\]

Their real rank is four, whereas \(H\) has rank three. Exact minimal dimension is therefore unstable at this observation table.

A useful empirical theory needs approximate realization and statistical identification in addition to exact categorical construction. This is not supplied by an isomorphism-based comparison calculus alone.

### Locality and composition require additional preservation laws

A realization determined by isolated tests need not remain adequate when coupled to another system. A local realization need not glue to a global one.

For an open-system language, the required result is not merely that each component admits reconstruction. It is that the relevant reconstruction preserves—or has a controlled comparison with—wiring, gluing, interventions, and any admitted feedback.

This is where contextads or a generalization could become consequential: they could specify the context calculus against which realization must be stable. But the observation action and preservation theorem would still have to be constructed. The context calculus and the reconstruction operation are not interchangeable.

### Formation of the observational vocabulary remains a separate problem

Testing-based reconstruction begins with enough of a probe language to formulate interactions. It can support refinement of tests and, in active learning settings, selection of distinguishing queries. It does not thereby establish how an arbitrary stream of experience yields the right primitives, interfaces, or explanatory decompositions.

The attached map identifies that larger target explicitly: discovering which latent distinctions are forced, rather than treating the latent space as primitive. categorical-phenomenology-metho…

The proposed organization can state such discovery problems precisely and compare partial solutions. No source examined establishes a general solution to them.

## Conclusion

**The best-supported organizing center is two-sided, context-sensitive realization—not a global ordering of theories and not one universal completion.**

Its concrete mathematical content would be:

\[
\boxed{
\text{structured testing correlations}
\;+\;
\text{categories of admissible realizations}
\;+\;
\text{specified reconstruction operations}
\;+\;
\text{preservation and obstruction theorems}.
}
\]

The strongest existing exact core is factorization-based realization; cylinder factorization connects it to Isbell-envelope machinery. *Comparative Smootheology* provides the clearest precedent for varying observational and structural requirements without declaring one approach universally strongest.

This recommendation has survived more than a formalizability test. There are actual constructions from observations, an explicit bridge between concept completion and behavioral realization, and an obstruction separating linear from stochastic realization. What has **not** been established is a single theory covering the entire method map, especially noisy inference and discovery of the observational vocabulary.

The practical mathematical choice is therefore to build around **testing correlations and admissible realizations**, and let hierarchies, adjunctions, completion operators, and comparison squares emerge where their preservation obligations can actually be proved.