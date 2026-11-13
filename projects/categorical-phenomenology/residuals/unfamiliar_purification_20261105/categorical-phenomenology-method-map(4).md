NOTE:
 - the aversion to institution theory is mostly accidentally since I had to explicitly prompt the AI to ignore institution theory to not over-index on it. Institutions are one way to factorize a passing/admissible interaction; cf. `towards-two-sided-context-sensitive-factorization-based-realization.md` for the more general idea

# Methods for generative categorical phenomenology

This map collects constructions and research leads for deriving structured models, concepts, interfaces, or theories from observational interaction. The [problem note](contextual-realization-problem-note.tex) states the current construction problems and their proof obligations; [supporting constructions](tomography-and-generative-realization.md) distinguish several mechanisms that the map must not identify. Entries are a non-exhaustive search aid. Their relevance is provisional: a candidate earns use by supplying a construction, preservation theorem, or obstruction for the intended observational question. A place in this map is not evidence of a unified theory or a required research agenda.

Four overlapping roles help locate possible uses: direct construction of observational structure; machinery for typing, composition, locality, or quantitative comparison; import targets with relevant inverse or identification problems; and boundary material requiring an explicit observation-to-structure connection. These roles are working classifications, revisable when a source supplies a different mechanism. The [absorption checklist](absorption-checklist-of-candidate-theories.md) can record a particular import's assumptions and warranted claims; the [observational-polarity note](observational-polarity-and-relevance-selection.md) retains the separate question of relevance selection.

References marked [~] are leads requiring verification before their claims are used. Quoted mathematical slogans below are scoped by the explicit qualifications at the relevant entry. The landscape does not claim completeness or novelty.

## I. Observation, testing, and state–property duality

These are the most literal instances of categorical phenomenology: a domain is known through how it interacts with a family of probes.

### Yoneda-type observational semantics

Topics: **Yoneda embeddings**; **Restricted Yoneda embeddings**; **Separating families / generators / cogenerators**; **Dense subcategories and the density theorem**; **Codense subcategories**; **Nerve constructions**; **Nerve–realization adjunctions**; **Restricted nerves**; **Density presentations**; **Codensity monads**.

The phenomenological interpretation is direct:

\[
X\mapsto \mathcal C(P-,X)
\]

turns an entity into its entire profile against a class of probes. Faithfulness separates parallel morphisms. Full faithfulness reconstructs morphisms between profiles in the image and identifies objects up to isomorphism there; it does not imply that every presheaf is realizable, or give a computationally stable inverse.

### Chu spaces and related interaction formalisms

The state/test pairing provides a direct comparison point.

A Chu space

\[
(X,A,\langle-,-\rangle:X\times A\to K)
\]

supplies entities, observations/tests, and an evaluation pairing as one candidate primitive. Duality exchanges the two sides.

Include:

Topics: **Chu spaces**; **Chu transforms**; **Chu duality**; **Chu construction**; **biextensional collapse**; **separated/extensional Chu spaces**; **Chu semantics of linear logic**; **Chu representations of closure spaces**; **state–property systems**; **topological systems**; **Chu-style dualities**.

FCA has been explicitly related to Chu systems, and Chu constructions have long served as an abstract state/test formalism. [~] [Formal concept analysis and lattice-valued Chu systems - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0165011412003776?utm_source=chatgpt.com); [~] [Chu duality theory and coalgebraic representation of quantum symmetries - ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0022404921003017?utm_source=chatgpt.com)

### Dialectica constructions

Less immediately empirical than Chu spaces, but structurally important:

Topics: **Dialectica categories**; **Dialectica interpretation**; **Dialectica/Chu comparison**; **lens-like Dialectica constructions**; **witness/counter-witness semantics**.

Where an observational problem has a witness/challenge interpretation, Dialectica constructions offer a candidate algebra of that polarity; this is not a claim that every observation problem has this form. [~] [GitHub - vcvpaiva/DialecticaCategories: A place to collect work on dialectica categories. · GitHub](https://github.com/vcvpaiva/DialecticaCategories?utm_source=chatgpt.com)

### Barwise–Seligman classification/channel theory

This is a predecessor for the token/type interaction interface.

Topics: **classifications**: tokens, types, satisfaction relation; **infomorphisms**; **information channels**; **channel cores**; **local logics**; **information flow through distributed classifications**.

A classification literally represents observations as token–type incidence, while infomorphisms transport the classification relation contravariantly. [~] [2.1 \*\*Classifications\*\*](https://www.rease.e.u-tokyo.ac.jp/read/en/archive/dp/f09/f0907.pdf?utm_source=chatgpt.com)

The classification interface is relevant; its ability to generate the required structures needs a separate argument.

## II. Concept formation and closure from observations

### Formal Concept Analysis

Already present, but its surrounding family is much larger:

Topics: **classical FCA**; **formal contexts**; **concept lattices**; **Galois connections**; **polarity**; **closure systems**; **attribute implications**; **Duquenne–Guigues bases**; **conceptual scaling**; **pattern structures**; **relational concept analysis**; **triadic/polyadic FCA**; **fuzzy FCA**; **multi-adjoint concept lattices**; **distributed FCA**; **rough concept analysis**.

In appropriate quantaloid-enriched settings, there is a related formulation: a relation/distributor generates Isbell/Kan adjunctions, whose fixed points produce generalized concept structures. Quantaloid-enriched category theory unifies FCA and rough-set constructions this way. [~] [Multi-adjoint concept lattices via quantaloid-enriched categories - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0165011420300762?utm_source=chatgpt.com)

### Rough set theory

A strong fit because it studies what distinctions survive restricted observational access.

Include:

Topics: lower/upper approximation; indiscernibility relations; tolerance relations; approximation spaces; rough concepts; dominance-based rough sets; many-valued rough sets; rough-set/FCA dualities.

The categorical bridge through quantaloid-enriched distributors is particularly relevant. [~] [Multi-adjoint concept lattices via quantaloid-enriched categories - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0165011420300762?utm_source=chatgpt.com)

### Closure and nucleus constructions

A very important generic family:

Topics: **closure operators**; **interior operators**; **nuclei**; **idempotent monads**; **idempotent comonads**; **reflective/coreflective subcategories**; **orthogonality classes**; **Galois insertions**; **MacNeille completion**; **Dedekind–MacNeille completion**; **Isbell completion**; **Isbell conjugacy**; **Isbell nuclei**; **Kan adjunction-induced completions**.

For the closure cases, a recurring operation is

\[
\text{raw observational possibilities}
\longrightarrow
\text{fixed points satisfying mutual consistency}.
\]

This is one construction family. Outside posetal/idempotent settings, reflexive objects and general monad algebras need not coincide; an Isbell adjunction does not by itself select the same realization as an image factorization.

## III. Observational equivalence, behavioral equivalence, and quotient formation

The relevant use is to determine which observations distinguish behaviors and which identifications support later operations.

### Universal coalgebra

The connection runs through behavior maps and their kernels.

Topics: **coalgebras for endofunctors**; **final coalgebra semantics**; **behavior maps**; **behavioral equivalence**; **bisimulation**; **simulation**; **coalgebraic modal logic**; **predicate liftings**; **relation liftings**; **trace semantics**; **coalgebraic trace semantics**; **coinduction**; **bisimulation up to**; **behavioral pseudometrics**; **coalgebraic minimization**.

Coalgebraic modal logic explicitly relates a language of tests to behavioral equivalence, and quantitative versions replace equality by behavioral distance. [~] [(Metric) Bisimulation Games and Real-Valued Modal Logics for Coalgebras](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2018.37?utm_source=chatgpt.com); [~] [Bisimulation for Weakly Expressive Coalgebraic Modal Logics](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CALCO.2017.4?utm_source=chatgpt.com)

These are candidate sources for observational saturation; expressive completeness and the intended equivalence require hypotheses.

### Process semantics

Import from concurrency theory:

Topics: **observational equivalence**; **contextual equivalence**; **testing equivalence**; **trace equivalence**; **failure equivalence**; **ready equivalence**; **bisimilarity**; **weak bisimulation**; **barbed congruence**; **applicative bisimulation**; **logical equivalence**; **Hennessy–Milner logics**.

These provide a huge laboratory for the question:

> Which testing contexts must be admitted so that indistinguishability is a congruence?

That question is central to categorical phenomenology.

### Open-map semantics

Especially interesting:

Topics: **Joyal–Nielsen–Winskel open maps**; **path categories**; **bisimulation via lifting properties**; **presheaf models of concurrency**.

This characterizes selected behavioral equivalences using lifting properties after a path category and its observations have been chosen.

### Quotients and exactness

Include:

Topics: regular epi–mono factorization; kernel pairs; congruences; effective equivalence relations; exact categories; Barr exactness; exact completions; quotient completions; localization; reflective localization; bicategories of fractions.

These are the categorical machinery for passing from presentations to observationally identified objects.

## IV. Automata, realization, and active theory formation

This is one of the clearest subfields.

### Automata theory

Include:

Topics: **Myhill–Nerode theory**; **minimal automata**; **syntactic monoids**; **residual languages**; **Brzozowski derivatives**; **Hankel matrices**; **weighted automata**; **tree automata**; **nominal automata**; **probabilistic automata**; **coalgebraic automata**; **categorical automata theory**.

The deep pattern is

\[
\text{experiments}
\to
\text{response profiles}
\to
\text{behavioral quotient}
\to
\text{minimal realization}.
\]

### Active automata learning

Central, not peripheral:

Topics: **Angluin \(L^*\)**; membership queries; equivalence queries; observation tables; closedness; consistency; counterexample refinement; discrimination trees; active model learning.

### CALF

Categorical Automata Learning Framework explicitly relates learning, testing, and minimization using categorical factorization machinery and generalizes beyond deterministic automata. [~] [CALF: Categorical Automata Learning Framework](https://arxiv.org/abs/1704.05676?utm_source=chatgpt.com); [~] [A Categorical Framework for Learning Generalised Tree Automata](https://arxiv.org/abs/2001.05786?utm_source=chatgpt.com)

### Coalgebra learning via duality

Also important because it separates **states** from **tests/formulas**, rather than letting both be words as in classical DFA learning. [~] [Coalgebra Learning via Duality | Springer Nature Link](https://link.springer.com/chapter/10.1007/978-3-030-17127-8_4?utm_source=chatgpt.com)

This separates the roles of states and tests without assuming that the same carrier represents both.

## V. Classical realization theory and system identification

The import question is how input-output observations generate internal state realizations.

Topics: **minimal realization theory**; controllability; observability; reachable subspaces; observable quotients; Kalman decomposition; Ho–Kalman realization; Hankel operators; realization rank; linear system identification; nonlinear realization; bilinear realization; rational series; behavioral realization; observable operator models; predictive-state representations; subspace identification; spectral learning; Koopman-operator models.

The conceptual equation is:

\[
\text{observable input-output behavior}
\rightsquigarrow
\text{internal state model}.
\]

System-identification literature explicitly formulates model construction as an observation-based realization problem involving identifiability, equivalence classes, and decomposition. [~] [System theory for system identification - ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0304407603001453?utm_source=chatgpt.com)

A possible comparison target is **automata minimization, linear realization, predictive-state representations, and learner-state extraction**. A common construction remains to be exhibited with each case's assumptions intact.

## VI. Statistical experiments, sufficiency, and information loss

This is another major pillar.

### Markov categories

Core topics:

Topics: stochastic morphisms; deterministic morphisms; copying/discarding; disintegration; Bayesian inversion; almost-sure equality; conditional independence; sufficient statistics; minimal sufficient statistics; ancillary statistics; conditional products; categorical probability.

Markov categories already provide synthetic formulations of sufficiency and conditional independence across multiple probability theories. [~] [A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0001870820302656?utm_source=chatgpt.com)

### Comparison of statistical experiments

This is particularly important.

Topics: **Blackwell informativeness preorder**; **Blackwell–Sherman–Stein theorem**; garbling; experiment comparison; deficiency; statistical sufficiency; decision equivalence; information orderings.

The categorical version of Blackwell comparison has already been developed in Markov categories. [~] [Representable Markov categories and comparison of statistical experiments in categorical probability - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0304397523002098?utm_source=chatgpt.com)

This gives categorical phenomenology a rigorous answer to:

> When does one observation interface contain at least as much decision-relevant information as another?

This preorder is a candidate when decision-relevant information is the governing comparison.

### Information geometry

Strong import target:

Topics: Fisher information; Fisher–Rao metric; Amari–Chentsov tensors; exponential/mixture connections; statistical manifolds; information projections; sufficient-statistic invariance; Čencov's theorem; natural gradient.

Sufficiency and invariance of information-geometric structures are linked under specified statistical and regularity assumptions; the exact direction and hypotheses of each characterization must be retained. [~] [Information geometry and sufficient statistics](https://arxiv.org/abs/1207.6736?utm_source=chatgpt.com)

This becomes the differential geometry of observationally meaningful parameter distinctions.

## VII. General probabilistic theories, effects, and tomography

This family supplies operational examples with explicit state and measurement structure.

### General probabilistic theories

Topics: state spaces; effect spaces; channels; instruments; convex operational models; state/effect duality; distinguishability; operational equivalence; composite systems; local tomography; process tomography; no-restriction hypotheses.

GPTs can equivalently begin from operational probability tables and quotient preparation/measurement procedures by observational equivalence. [~] [General probabilistic theories: An introduction - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0370157323002752?utm_source=chatgpt.com)

This supplies a concrete preparation/measurement quotient; reconstructing further structure requires additional assumptions.

### Effectus theory

Already in the folder; surrounding topics include:

Topics: effect algebras; effect modules; predicates; states; validity pairing; instruments; comprehension; quotients; assert maps; sequential products; effect monoids; state–effect triangles.

Effectus theory is explicitly organized around state/effect duality and Born-style validity. [~] [An Introduction to Effectus Theory](https://arxiv.org/abs/1512.05813?utm_source=chatgpt.com)

### Categorical quantum mechanics and operational process theories

Relevant pieces:

Topics: symmetric monoidal process theories; dagger compact categories; CPM construction; CP* construction; environment structures; purification; compact closure; process-state duality; Choi–Jamiołkowski representations; quantum combs; process tomography; local tomography; causal process theories.

Process tomography and tomographic locality have explicit formulations in general process theories. [~] [Process Tomography in General Physical Theories](https://www.mdpi.com/2073-8994/13/11/1985?utm_source=chatgpt.com)

The important research question is not “quantum category theory” generically; it is **what observational families determine processes, and under what compositional restrictions?**

## VIII. Learning as observationally driven parameter dynamics

This is the gradient-learning wing.

### Parameterization machinery

Topics: **Para construction**; actegories; parametrized morphisms; parameterized optics; parameterized lenses; double-categorical Para; parameter-sharing / weight tying.

### Learners

Topics: category of learners; Backprop-as-Functor; update/request maps; compositional supervised learning.

Backpropagation admits a monoidal-functorial formulation from parametrized functions into compositional learners. [~] [Backprop as Functor: A compositional perspective on supervised learning](https://arxiv.org/abs/1711.10455?utm_source=chatgpt.com)

### Lenses and optics

Topics: simple lenses; dependent lenses; symmetric lenses; Bayesian lenses; optics; mixed optics; dependent optics; weighted optics; polynomial lenses; profunctor optics.

Lenses matter because theory formation is frequently bidirectional:

\[
\text{prediction forward},
\qquad
\text{error/evidence backward}.
\]

### Categorical differentiation

Topics: Cartesian differential categories; reverse differential categories; tangent categories; differential categories; differential restriction categories; Faà di Bruno constructions; differential combinators; categorical automatic differentiation; CHAD; reverse-mode AD; functorial AD.

The modern categorical learning framework combines parametrized maps, lenses, and reverse derivatives, covering several gradient optimizers and loss constructions. [~] [Categorical Foundations of Gradient-Based Learning](https://arxiv.org/abs/2103.01931?utm_source=chatgpt.com)

### Optimizers as dynamical structure

Include:

Topics: gradient descent; momentum; Adam; AdaGrad; natural gradient; mirror descent; optimizer state; learning-rate schedules.

The realization problem asks which parts of parameter state remain observationally necessary **under the intervention algebra generated by training**.

Static model semantics and the state needed for learning answer different questions.

## IX. Bayesian learning and probabilistic inference

Distinct from gradient learning.

Topics: Bayesian inversion; Bayesian updating; disintegration; conjugate priors; Bayesian filtering; hidden Markov models; Kalman filters; particle filters; message passing; factor graphs; belief propagation; expectation propagation; variational inference.

Categorically relevant infrastructure:

Topics: Markov categories; probability monads; Giry/Kleisli constructions; affine monads; graded probability constructions; Bayesian lenses; optics for inference.

Categorical Bayesian inversion is already well developed, including noncommutative variants. [~] [Inverses, disintegrations, and Bayesian inversion in quantum Markov categories](https://arxiv.org/abs/2001.08375?utm_source=chatgpt.com)

## X. Causal and interventional phenomenology

Without additional identifying assumptions, passive observations may leave distinct causal structures compatible with the data. Passive and interventional tests therefore need separate semantics.

Include:

Topics: structural causal models; intervention algebras; causal Bayesian networks; \(do\)-interventions; counterfactual models; causal identifiability; causal abstraction; causal representation learning; experiment design for causality.

Categorical developments:

Topics: **causal theories**; categorical Bayesian networks; causal Markov categories; string-diagrammatic causal inference; categorical interventions; causal effect calculi.

Fong's causal theories encode variables and causal information flow in symmetric monoidal categories. [~] [Causal Theories: A Categorical Perspective on Bayesian Networks](https://arxiv.org/abs/1301.6201?utm_source=chatgpt.com)

An especially important categorical-phenomenological distinction is

\[
\text{observational equivalence}
\neq
\text{interventional equivalence}.
\]

Preserve this distinction whenever the intended queries include interventions.

## XI. Decomposition theory

This is probably the second major pillar beside observation.

### Decomposition spaces / 2-Segal spaces

Include:

Topics: decomposition spaces; unital 2-Segal spaces; incidence coalgebras; objective incidence algebras; Möbius inversion; Möbius decomposition spaces; CULF maps; decalage; restriction species; directed restriction species; Waldhausen \(S\)-construction; Hall algebra constructions.

Decomposition spaces weaken Segal composition precisely so as to retain coherent decomposition data and support incidence coalgebras. [~] [Decomposition spaces in Combinatorics](https://arxiv.org/abs/1612.09225?utm_source=chatgpt.com)

### Operadic decomposition

Topics: operads; colored operads; symmetric operads; nonsymmetric operads; cyclic operads; modular operads; PROPs; PROs; Lawvere theories; generalized multicategories; opetopes; dendroidal sets; operadic nerves; Feynman categories; polynomial monads; operadic categories.

Phenomenologically, these specify **which decompositions count as explanations of a composite observation**.

### Multicategories and virtual equipments

Already present, but expand to:

Topics: virtual double categories; virtual equipments; framed bicategories; proarrow equipments; double categories; pseudo double categories; equipments of profunctors; internal categories.

These are candidate typing environments when interactions exist before representable processes; none is selected by that resemblance alone.

### Polynomial structures

Topics: polynomial functors; polynomial monads; containers; species; analytic functors; familial functors; parametric right adjoints; ornaments; polynomial lenses.

These matter for **shape/content decomposition** and reconstruction of structured data types.

## XII. Open systems and interface formation

Open-system category theory is strongly relevant whenever observations occur at boundaries.

Topics: spans; cospans; structured cospans; decorated cospans; corelations; decorated corelations; hypergraph categories; wiring-diagram categories; props; open Petri nets; open reaction networks; open Markov processes; open dynamical systems; black-boxing functors; behavioral semantics of open systems.

Structured and decorated cospans provide double-categorical models of systems with explicit interfaces and composition by gluing. [~] [#13517 - Structured versus Decorated Cospans](https://compositionality.episciences.org/13517?utm_source=chatgpt.com); [~] [Open Systems: A Double Categorical Perspective](https://arxiv.org/abs/2008.02394?utm_source=chatgpt.com)

For categorical phenomenology, **black-boxing** is especially important:

\[
\text{internal presentation}
\longrightarrow
\text{boundary behavior}.
\]

Then one can study inverse black-boxing: which internal structures realize a boundary behavior?

The generative problem is the inverse construction, including its nonuniqueness and preservation requirements.

## XIII. Categorical systems theory and cybernetics

The connection concerns reconstruction of systems from interface behavior.

Topics: indexed categories of systems; dynamical-system fibrations; lenses as open dynamical systems; charts between systems; parametrized systems; dependent interfaces; Markov fibrations; categorical cybernetics; stochastic open systems; feedback structures; traced monoidal categories; signal-flow categories; control as composition.

Categorical systems theory uses indexed categories/fibrations to organize families of dynamical systems and lenses to describe bidirectional interfaces. [~] [Categorical Systems Theory](https://erischel.com/myers-cst/?utm_source=chatgpt.com)

The phenomenological research problem is then:

> Given only interface trajectories, perturbation responses, or closed-loop observations, what system object is reconstructed?

That reconnects categorical systems theory to realization rather than merely composition.

## XIV. Descent, sheaves, and local-to-global reconstruction

The relevant question is when construction commutes with localization and gluing.

### Classical machinery

Topics: presheaves; sheaves; sites; Grothendieck topologies; descent; effective descent; codescent; stacks; prestacks; gerbes; Čech nerves; hypercovers; sheafification; cosheaves; derived descent.

### Applied sheaf theory

Topics: cellular sheaves; cellular cosheaves; sheaf cohomology; sheaf Laplacians; sheaf diffusion; sensor fusion; distributed consistency; network coding; sheaf neural networks; sheaf-based signal processing.

Applied sheaf theory is now used substantially in data science and machine learning, especially for locally constrained information and sheaf diffusion. [~] [Sheaf theory: from deep geometry to deep learning](https://arxiv.org/abs/2502.15476?utm_source=chatgpt.com)

### Sheaf-theoretic contextuality

Critical bridge to observation theory:

Topics: empirical models; compatibility/no-signaling; global sections; contextuality; cohomological obstruction; contextual fraction.

This gives a precise theory of when locally consistent observation data **cannot arise from a single global hidden realization**.

This is one precise obstruction family; it does not characterize every failure of realization.

### Factorization algebras

Worth adding:

Topics: factorization algebras; cosheaf-like observables; local-to-global composition of observables; factorization homology.

Potentially useful where the relevant locality operation is disjoint union/decomposition rather than ordinary covering.

## XV. Indexed categories, fibrations, and varying observational regimes

These describe variation across contexts; generative content requires constructions within or across the fibers.

Topics: Grothendieck fibrations; opfibrations; bifibrations; indexed categories; pseudofunctors into \(\mathbf{Cat}\); Grothendieck construction; comprehension categories; cartesian fibrations; cocartesian fibrations; double fibrations; equipment fibrations.

These model dependence of theory on:

Topics: experimental context,; available probes,; interface type,; data regime,; locality,; parameterization,; hypothesis class..

The family

\[
D\longmapsto \mathsf{Real}(D)
\]

can be retained as an indexed family when its reindexing maps and coherence have been supplied.

## XVI. Enrichment and quantitative phenomenology

Exact equality is too brittle for empirical theory formation.

### Quantale/quantaloid enrichment

Topics: Lawvere metric spaces; quantale-enriched categories; quantaloid-enriched categories; fuzzy relations; enriched distributors; enriched profunctors; enriched Yoneda; enriched Isbell completion; enriched Cauchy completion; enriched FCA.

Lawvere's observation that generalized metric spaces are enriched categories makes metric observational indistinguishability categorically native rather than an added numerical structure. [~] [Untitled](https://raw.githubusercontent.com/mattearnshaw/lawvere/master/pdfs/1973-metric-spaces-generalized-logic-closed-categories.pdf?utm_source=chatgpt.com)

### Behavioral distances

Topics: bisimulation pseudometrics; Kantorovich liftings; Wasserstein liftings; Hausdorff liftings; probabilistic behavioral metrics; logical metrics.

### Approximate category theory

Potential frontier:

Topics: approximate commutativity; metric-enriched universal properties; approximate adjunctions; quantitative equational logic; enriched orthogonality; stability of universal constructions.

Approximate claims need a declared metric, error model, or other comparison, and a preservation bound.

## XVII. Inverse problems, identifiability, and regularization

This is an enormous noncategorical import target.

Topics: inverse problems; forward operators; identifiability; structural identifiability; practical identifiability; estimability; ill-posedness; regularization; Tikhonov regularization; sparsity regularization; variational reconstruction; inverse scattering; inverse imaging; tomography; blind deconvolution; phase retrieval.

A useful three-way split is:

\[
\text{existence},\qquad
\text{uniqueness/identifiability},\qquad
\text{stability}.
\]

Identifiability addresses uniqueness but not stability; categorical discussions that stop at faithfulness risk missing this. [~] [What can be estimated? Identifiability, estimability, causal inference and ill-posed inverse problems](https://arxiv.org/abs/1904.02826?utm_source=chatgpt.com)

This deserves a dedicated “quantitative realization” wing.

## XVIII. Tomography and probe design

Beyond quantum tomography:

Topics: state tomography; process tomography; gate-set tomography; compressed sensing tomography; adaptive tomography; local tomography; ancilla-assisted tomography; system identification; tensor tomography; geometric tomography; inverse Radon transforms.

Categorical concepts to connect:

Topics: separating families; generators; dense probe subcategories; informationally complete measurements; faithful states; process-state correspondences.

The deeper question is not tomography as a technique but:

\[
\boxed{\text{What families of admissible probes are sufficient for reconstruction?}}
\]

## XIX. Experimental design and active observation

This extends a static reconstruction problem to the choice of further evidence.

Static phenomenology asks what observations imply.

Active phenomenology asks **which observation should be performed next**.

Include:

Topics: optimal experimental design; Bayesian experimental design; active learning; query learning; adaptive sensing; adaptive tomography; sequential experiment design; value of information; expected information gain; D-optimality; A-optimality; E-optimality; mutual-information design; uncertainty sampling; falsification-oriented experiment selection.

One proposed target is an algebra of probes plus a strategy selecting future probes according to the current realization category.

A common account would need to recover the distinct oracle, probability, cost, and convergence assumptions of those settings.

## XX. Topological structure learned from data

Strong adjacent/core bridge.

### Topological data analysis

Topics: persistent homology; persistence modules; barcodes; Vietoris–Rips complexes; Čech complexes; Mapper; Reeb graphs; zigzag persistence; multiparameter persistence; persistence sheaves; interleaving distance; stability theorems.

The phenomenological transformation is literally

\[
\text{metric/relational observations}
\to
\text{topological invariants}.
\]

### Functorial clustering

Especially relevant because it treats clustering algorithms as functors and uses naturality as a stability/coherence requirement across data transformations. [~] [Functorial hierarchical clustering with overlaps - ScienceDirect](https://doi.org/10.1016/j.dam.2017.10.015?utm_source=chatgpt.com)

Include:

Topics: functorial hierarchical clustering; overlapping clustering; single-linkage universal characterizations; categorical clustering axioms.

### Dowker theory

Very worth adding.

Given a relation \(R\subseteq X\times Y\), there are dual simplicial complexes on \(X\) and \(Y\) with equivalent homotopy type.

That is another state/test duality:

\[
\text{objects}\leftrightarrow\text{observables}
\]

producing equivalent reconstructed topology.

Potentially a deep bridge between **FCA-style concept reconstruction** and **TDA-style topological reconstruction** from the same incidence data.

## XXI. Abstract interpretation and approximation semantics

The relevant import is soundness and completeness of information-losing approximations.

Topics: abstract interpretation; concrete/abstract domains; Galois connections; Galois insertions; closure operators; sound abstraction; completeness of abstractions; best correct approximation; reduced products; widening/narrowing; domain refinement; partition refinement.

Why central?

Because it studies

\[
\text{concrete behavior}
\to
\text{observable abstraction}
\]

with explicit laws for exactly which properties are preserved.

Categorical phenomenology needs this language for distinguishing:

Topics: lossless reconstruction,; sound coarse realization,; sufficient abstraction,; merely heuristic feature extraction..

## XXII. Domain theory and information systems

Potentially important for partial observation.

Topics: dcpos; Scott domains; algebraic domains; continuous domains; information systems; Scott topology; approximation relations; ideal completion; domain equations; powerdomains.

Algebraic domains represent elements as directed suprema of compact approximants; continuous domains permit the broader way-below approximation relation. Arbitrary domains need not be algebraic. That makes it relevant whenever theories arise through increasing evidence rather than one complete observation table.

## XXIII. Symmetry, gauge, and non-identifiability

Retain symmetries when they affect reconstruction, identifiability, or intervention.

Topics: group actions; groupoids; action groupoids; quotient groupoids; orbifolds; stacks; quotient stacks; gauge equivalence; reparameterization symmetry; moduli spaces; moduli stacks; Morita equivalence; categorical equivalence; weak equivalence; homotopy quotient.

The point is:

\[
\text{multiple presentations}
\neq
\text{multiple phenomena}.
\]

For neural networks, latent-variable models, dynamical systems, and quantum representations, nonidentifiability is often a symmetry problem rather than mere failure of injectivity.

A groupoid or category is needed when automorphisms or comparison maps affect the intended query; a set quotient may suffice for other queries.

## XXIV. Homotopy-theoretic and higher-categorical reconstruction

Potentially frontier-level rather than routine.

Topics: simplicial categories; simplicial sets; Segal spaces; complete Segal spaces; quasicategories; \((\infty,1)\)-categories; model categories; localization; Dwyer–Kan localization; homotopy colimits; homotopy limits; derived Kan extensions; derived descent; homotopy coherent diagrams.

The motivation is not “higher category theory is sophisticated.” It is concrete:

If presentations have transformations, transformations have transformations, and observational equivalence itself carries higher coherence, then taking a set of equivalence classes destroys structure.

The correct realization object can be a homotopy type.

## XXV. Type discovery and completion

A direct bridge to the “typed decomposition from untyped observations” part.

Topics: Karoubi/Cauchy completion; idempotent splitting; retract completion; exact completion; regular completion; free finite-limit completion; free cocompletion; Ind-completion; Pro-completion; localization; completion under selected weighted limits/colimits; enriched completion; Segal completion; Rezk completion.

These can construct new **interfaces/types/ideal objects** relative to selected universal properties. Their empirical justification is a separate obligation.

Particularly interesting research question:

> Which completion operation corresponds to which empirical justification for introducing a latent type?

## XXVI. Category-theoretic logic of predicates and observations

Not institution theory.

Useful pieces of categorical logic include:

Topics: subobject fibrations; predicate fibrations; hyperdoctrines; doctrines; regular logic; coherent logic; geometric logic; triposes; comprehension; quantifiers as adjoints; fibrational logic; categorical modal logic; coalgebraic modal logic; linear logic; graded/modal type systems.

The relevant part is not “theories have models.” It is the internal organization of **tests, predicates, observables, and quantification over contexts**.

## XXVII. Stone-type dualities and syntax–observation reconstruction

A very promising neighboring continent:

Topics: Stone duality; Priestley duality; Stone–Čech ideas; spectral dualities; locale theory; point-free topology; Jónsson–Tarski duality; coalgebraic duality; natural dualities; Chu duality; Isbell duality.

These repeatedly exhibit the pattern

\[
\text{space/state structure}
\leftrightarrow
\text{algebra of observations}.
\]

For the named classes where the duality holds, investigate its **reconstruction theorem from a complete observable algebra**, retaining the relevant topology, algebraic hypotheses, and notion of completeness.

## XXVIII. Relational/profunctorial semantics

Likely foundational.

Topics: profunctors; distributors; modules; bimodules; enriched profunctors; quantaloid distributors; relational composition; allegories; regular categories; equipments of relations; bicategories of relations.

Why important: raw observation is very often **relational before it is functional**.

\[
\text{entity}\;\not\to\;\text{observable value}
\]

may instead be a relation, stochastic kernel, score, compatibility degree, or witness space.

Encoding such interactions as functions can be exact if the codomain retains the relation, distribution, or witnesses; the risk is collapsing those values to a deterministic scalar.

## XXIX. Relation lifting and predicate lifting

This deserves explicit visibility because it connects structure and observation.

Topics: Barr relation lifting; coalgebraic relation lifting; predicate lifting; Kantorovich lifting; Wasserstein lifting; codensity lifting; fibrational lifting; logical predicates; logical relations.

These tell how a system constructor transports:

Topics: behavioral relations,; predicates/tests,; metrics,; equivalences..

That is almost exactly the technical problem of ensuring observational structure survives model constructors.

## XXX. Factorization systems and orthogonality

One of the key methodological backbones.

Topics: weak factorization systems; orthogonal factorization systems; epi–mono systems; regular epi–mono systems; image factorizations; comprehensive factorization; active–inert factorization; generic/free factorization; lifting properties; orthogonality classes; cylinder factorization systems.

These give a generic grammar for:

\[
\text{generate/reach}
\quad+\quad
\text{separate/observe}.
\]

They already appear explicitly in categorical automata learning. [~] [CALF: Categorical Automata Learning Framework](https://arxiv.org/abs/1704.05676?utm_source=chatgpt.com)

The generating/separating interpretation must be established for the chosen factorization system; a weak factorization system alone does not give the uniqueness of an orthogonal one.

## XXXI. Kan extensions as inference operators

Another generic method worth foregrounding.

Topics: left Kan extension; right Kan extension; pointwise Kan extensions; enriched Kan extensions; Kan lifting; codensity; data migration by Kan extension.

Interpretations:

Topics: left Kan extension: freely propagate/generate information;; right Kan extension: infer constraints compatible with observations;; density/codensity: reconstruct entities from probe responses..

These interpretations require a specified indexing functor, value category, and existence hypotheses. A Kan extension is universal in that diagrammatic setting; it is not automatically justified inference, logical conservativity, or an approximation guarantee.

## XXXII. Data integration and categorical databases

Strong applied fit if kept observation-oriented.

Topics: functorial data migration; database schemas as categories; instances as functors; \(\Delta,\Sigma,\Pi\) data migration; ologs; categorical databases; schema mappings; data integration; entity resolution; knowledge representation.

The interesting question is not database implementation but reconstruction of coherent latent structure from heterogeneous partial observations.

## XXXIII. Representation learning and latent-variable models

These are mostly **import targets**, not yet categorically solved.

Topics: representation learning; latent variable models; autoencoders; variational autoencoders; identifiable VAEs; disentanglement; nonlinear ICA; factor analysis; tensor decomposition; latent-state models; state-space models; world models.

The relevant realization question is:

\[
\text{Which latent distinctions are forced by observational/interventional structure?}
\]

rather than treating a latent vector space as primitive.

The relevant mathematical bridges are identifiability, symmetry groupoids, completion, sufficient statistics, and behavioral realization.

## XXXIV. Model reduction and coarse graining

Another major bridge.

Topics: lumpability; bisimulation quotienting; state aggregation; balanced truncation; singular perturbation; coarse graining; renormalization-style transformations; abstraction; behavioral quotient; Markov-chain lumping; MDP homomorphisms; approximate bisimulation.

These study when reduced models preserve specified observable behavior.

This is directly categorical-phenomenological once the preserved test family is made explicit.

## XXXV. Reinforcement learning and control

Not all RL fits. The relevant parts are:

Topics: state abstraction; bisimulation metrics; successor features; predictive representations; option discovery; task decomposition; compositional RL; MDP homomorphisms; model-based RL; system identification; world-model learning.

Categorical work now treats MDPs and task composition using categorical constructions such as pushouts and pullbacks. [~] [Categorical Semantics of Compositional Reinforcement Learning](https://jmlr.org/papers/v26/24-0197.html?utm_source=chatgpt.com)

The most interesting connection to the program is not categorical composition of already-known MDPs; it is **learning observationally sufficient state abstractions that remain sufficient under control interventions**.

## XXXVI. Open games and compositional decision processes

Moderate-to-strong fit:

Topics: open games; compositional game theory; selection functions; continuation-based semantics; game-theoretic lenses; equilibrium functions; stochastic open games.

Their conceptual relevance is that what counts as adequate behavior depends on a **continuation/context supplied by the environment**.

This makes them a sophisticated source of context-indexed observational equivalence.

## XXXVII. Resource theories

A useful but conditional fit.

Topics: symmetric monoidal resource theories; ordered resource theories; convertibility preorders; monotones; catalysis; contextual resources; quantum resource theories.

These become phenomenological when resource distinctions are reconstructed from observable conversion experiments rather than postulated beforehand.

## XXXVIII. String diagrams and graphical calculi

These are not a theory of phenomenology by themselves, but an essential method:

Topics: monoidal string diagrams; traced diagrams; compact closed diagrams; double-category diagrams; equipment diagrams; graphical optics; graphical probability; tensor-network calculi.

Their main benefit is exposing admissible contexts and substitution operations visually—the things observational equivalence must respect.

## XXXIX. Scientific model discovery

Mostly import target, but important.

Topics: symbolic regression; equation discovery; sparse identification of nonlinear dynamics/SINDy; causal discovery; invariant discovery; conservation-law discovery; program synthesis from examples; inductive logic programming; grammar induction; automata inference; scientific machine learning.

Categorical phenomenology could provide the missing common structure:

\[
\text{observations}
\to
\text{candidate generators/relations}
\to
\text{contextual tests}
\to
\text{quotient/completion}
\to
\text{structured law}.
\]

## XL. Minimality, compression, and explanatory economy

This is another area worth importing carefully.

Topics: minimal sufficient statistics; minimum description length; algorithmic sufficient statistics; information bottleneck; rate–distortion theory; predictive information; minimal realization; state complexity; causal-state reconstruction; computational mechanics.

The comparison question is:

> Minimal with respect to which preserved observational law?

Otherwise “minimality” is undefined.

This is particularly important because automaton minimization, sufficient statistics, coarse graining, and representation learning all use different stakeholder laws.

## XLI. Computational mechanics and predictive-state reconstruction

This provides a probabilistic comparison for continuation-based state formation.

Topics: causal states; \(\epsilon\)-machines; predictive equivalence; statistical complexity; predictive state reconstruction; computational mechanics.

The construction

\[
x_{\text{past}}\sim y_{\text{past}}
\iff
P(\text{future}\mid x_{\text{past}})
=
P(\text{future}\mid y_{\text{past}})
\]

defines predictive equivalence, a probabilistic analogue of residual-state identification. Conditional distributions need their own existence and almost-sure qualifications; zero-probability histories are not assigned unique conditionals for free.

That is almost tailor-made for categorical generalization.

## XLII. Reusable categorical methods

Candidate operators, to use where their hypotheses and preserved queries are instantiated:

Topics: Yoneda reduction; representability; density/codensity; ends/coends; Kan extension; adjunction; monadicity/comonadicity; factorization; orthogonality; closure/nucleus construction; localization; exact completion; Cauchy/Karoubi completion; Grothendieck construction; enrichment; change of base; profunctor composition; mates correspondence; Beck–Chevalley conditions; Frobenius reciprocity; descent; sheafification; nerve/realization; coinduction; bisimulation; lifting; black-boxing; quotienting; idempotent splitting; distributive laws; Day convolution; convolution algebras; incidence coalgebras; categorical trace; higher localization.

Their reuse requires a construction-specific preservation argument; the list itself proves no transfer.

## Candidate entry points

The following entry points connect a candidate literature to a concrete generative or preservation question. They are a possible search order, not a ranking established by comparison:

1. **Chu spaces + Barwise–Seligman classifications/channels** for primitive state/test interaction.
2. **Universal coalgebra + coalgebraic modal logic** for behavioral observation, test expressivity, and quotient formation.
3. **Classical realization theory/system identification** for the observation-to-minimal-model problem.
4. **Blackwell comparison + categorical sufficient statistics** for ordering observational interfaces by informativeness. Markov categories already support this direction. [~] [Representable Markov categories and comparison of statistical experiments in categorical probability - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0304397523002098?utm_source=chatgpt.com)
5. **Abstract interpretation** for controlled information loss.
6. **Inverse-problem theory** for separating identifiability from stability.
7. **Experimental design/active learning** for moving from passive phenomenology to adaptive observation.
8. **Symmetry/groupoid/moduli methods** for non-identifiable presentations.
9. **Computational mechanics/predictive states** as the probabilistic counterpart of Myhill–Nerode.
10. **Dowker/TDA/functorial clustering** for deriving topology rather than algebra or logic from observations.
11. **Open-map/bisimulation machinery** for contextual equivalence by lifting.
12. **Approximate/enriched reconstruction** so the theory survives finite/noisy data.

A possible synthesis asks which cases instantiate parts of the following dependency sketch, and with what compatibility laws:

\[
\boxed{
\begin{array}{c}
\text{preparations / phenomena}\\
\downarrow\\
\text{interaction with admissible probes}\\
\downarrow\\
\text{response object}\\
\downarrow\\
\text{contextual saturation}\\
\downarrow\\
\text{observational identification}\\
\downarrow\\
\text{structured completion / realization}\\
\downarrow\\
\text{minimality, locality, stability}\\
\downarrow\\
\text{new interventions / observations}
\end{array}}
\]

while differing in **what counts as a probe, what contexts close the probes, what structure is completed, what equivalence is admissible, and what invariants the reconstruction must preserve**.

Probe class, contextual closure, structural doctrine, observational law, and preservation law are comparison variables. The sequence is a research sketch, not a mandatory pipeline: active learning can revise its own tests, and noncommuting constructions require explicit comparison or obstruction results.
