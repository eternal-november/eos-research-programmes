# Primary source audit for categorical phenomenology

## Assessment

The cited literature already supports substantial construction as well as comparison. A defensible research programme must distinguish formal generation of mathematical objects, recovery of a system from experiments, and discovery of an explanatory structure that was not supplied in advance. These are different achievements. A categorical presentation does not by itself establish the third.

The entries below state existing results and their conditions. The final section proposes research targets rather than claiming their novelty. All page references are **one-based PDF page numbers**, including for Stacey. The review is a focused comparison, not an exhaustive novelty search.

## Stacey on test structures and changes of framework

[Andrew Stacey, Comparative Smootheology](https://arxiv.org/pdf/0802.2225), §§3–4, especially Definition 3.1, PDF p. 7; Definitions 3.6–3.8, pp. 9–10; Proposition 4.1, p. 16; Proposition 4.7, pp. 18–19; Definition 4.10, p. 20.

**Already supplied.** Given an underlying category U, test category T and faithful functor J:T→U, virtual objects have an underlying object X and compatible incoming/outgoing test families. Composition must land in the test category. Forcing conditions specify sufficient trials and generate categories satisfying selected closure requirements. Fibres over X are complete lattices. The paper constructs comparison functors by changing forcing conditions, test objects and underlying categories, then studies concrete smooth-space relationships.

**Conditions and boundary.** The framework supplies a recipe once the ambient category, tests and forcing choices are given; it is not a statistical procedure for discovering those choices. Smallness matters for whether fibres are sets. For− and For+ are not automatically lower and upper approximations, hence should not automatically be called coreflectors and reflectors: the counterexample on PDF p. 19 shows the intended bound can fail. Proposition 4.7 controls particular changes. Test-change analysis introduces U-adequacy, a detectability condition on non-test morphisms.

**Implication.** Generating structure from two-sided tests, or comparing different test regimes, cannot alone carry a novelty claim.

## Garner on a universal construction from two-sided data

[Richard Garner, The Isbell monad](https://arxiv.org/pdf/1410.7108), introductory construction, PDF pp. 2–3; Theorem 3.3, pp. 11–12; Theorem 4.1, pp. 14–16; Theorem 5.1, p. 17; Theorem 6.1, pp. 19–20.

**Already supplied.** An Isbell-envelope object combines a small presheaf, small copresheaf and natural pairing into the hom-functor. Theorem 3.3 identifies the envelope as the free category with a cylinder factorisation system on the original category. Cylinder factorisations interpolate a natural family of maps through an essentially unique intermediate object, relative to orthogonal cocone/cone classes. Theorem 4.1 identifies the pseudomonad's pseudoalgebras with cylinder factorisation systems. Morphisms preserve both distinguished classes, with lax/colax variants preserving one side.

**Conditions and boundary.** Locally small categories and the smallness restrictions on presheaves and diagram indexing are substantive. The universal property concerns mathematical completion relative to a specified category and factorisation structure. It does not say that arbitrary empirical pairings are noise-free, identify a unique physical implementation, or supply a finite learning algorithm.

**Implication.** Two-sided probe/response pairing, universal interpolation and a canonical completion are established machinery. A new result must identify additional hypotheses, computational consequences or a genuinely different universal problem.

## CALF on learning hypotheses and comparing systems

[Gerco van Heerdt, Matteo Sammartino and Alexandra Silva, CALF](https://arxiv.org/pdf/1704.05676), Definitions 1–8, PDF pp. 4–6; Theorem 9, p. 6; Theorem 17, p. 9; Theorem 21, p. 12; Appendix A.

**Already supplied.** A wrapper S→Q→P represents partial access to an unknown target. Its observable composite factors through a hypothesis H. Closedness and consistency induce algebraic dynamics on H. This explicitly generates a structured hypothesis from observations, not merely a similarity score. The framework relates learning, minimisation and conformance testing, with deterministic and linear weighted automata instances.

**Conditions.** It assumes an epi/mono factorisation system; Theorem 9 requires the dynamics functor to preserve its epi class. Automata recovery uses initial input and final output systems. Theorem 17 recovers Q up to automaton isomorphism if Q is observable, the wrapper is output- and dynamics-consistent, and S→Q is in the epi class; dually, reachability, initial/dynamics closedness and Q→P in the mono class suffice. Theorem 21 makes comparison conditional on corresponding coverage and separation assumptions. Practical W-method testing additionally uses a state bound.

**Boundary.** A finite table agreeing with a target is not unconditional identification. A proposed learning construction must show what it adds to these existing hypotheses, operations or guarantees.

## Lorenz and Tull on queries and mechanisms

[Robin Lorenz and Sean Tull, Causal and Compositional Abstraction](https://arxiv.org/pdf/2602.16612), Definitions 14–16, PDF pp. 17–18; Definition 46 and Proposition 47, p. 33; Definitions 49–50 and Theorem 51, pp. 36–38; discussion, pp. 51–52.

**Already supplied.** Query translations and natural transformations formalise low/high-level abstraction. Component-level abstraction additionally translates high-level mechanisms into low-level diagrams, respecting the query interpretation; it implies query-level abstraction. Theorem 51 characterises when a constructive causal abstraction extends to mechanism level.

**Conditions.** The theorem assumes every high-level non-input variable is an output and low-level input variables admit normalised states (with a weaker cancellation alternative in its footnote). The partition must be simple for Cartesian structure, extra-simple for Markov structure, and extra-simple plus full for cd structure. Thus the chosen equations of the structure category change what counts as an admissible mechanistic explanation.

**Boundary.** The results formalise and characterise candidate abstractions and include constructions relating them; they do not provide a general data-driven algorithm discovering explanatory variables. The causal treatment assumes acyclicity and exact consistency. Approximation and cyclic extension are proposed directions here, but approximate causal abstraction already exists in the cited literature. Neither approximate comparison nor mechanism-sensitive coherence is an unoccupied topic merely because it appears as a possible extension in this paper.

## Nanda and colleagues on mechanistic discovery and prediction

[Neel Nanda and colleagues, Progress measures for grokking via mechanistic interpretability](https://arxiv.org/pdf/2301.05217), §§4–6, especially ablations and progress measures, PDF pp. 7–9.

**Already supplied.** For small transformers learning modular addition, the paper reconstructs a Fourier-based computation using weight/activation analysis and ablations. It derives restricted and excluded losses that expose circuit formation before the abrupt improvement in test performance. This is already explanatory structure discovery with intervention-based checks, although it is not phrased as a general categorical construction.

**Conditions and boundary.** The experiments have full internal model access and a tractable algorithmic task. The restricted/excluded metrics use key frequencies identified from the final mechanism. The discussion explicitly identifies substantial manual work, task-specific metrics and the absence of a general ex ante criticality criterion predicting transition time. The experiments are not a theorem that every grokking system has this mechanism.

**Implication.** Re-describing the known Fourier circuit is an important reproduction baseline, not evidence of new discovery. A stronger target would infer the explanatory coordinates without using the final solution, validate them by held-out interventions, and predict something not available from ordinary loss curves.

## Active learning as a direct construction precedent

[Dana Angluin, Learning Regular Sets from Queries and Counterexamples](https://homepages.math.uic.edu/~lreyzin/papers/angluin87.pdf), §2, Theorem 1, PDF p. 5; Theorem 6, p. 11.

**Already supplied.** L* creates states and transitions from rows of a closed, consistent observation table and revises the table with counterexamples. With a minimally adequate teacher it terminates with the minimum DFA, up to isomorphism, in polynomial time in the number of target states and longest counterexample, for a fixed known finite alphabet.

**Conditions and boundary.** The teacher supplies correct membership answers and equivalence answers with counterexamples. The latter is a stronger capability than collecting a finite empirical dataset. The paper separately treats stochastic approximate learning. Replacing the equivalence oracle by finite tests must preserve the distinction between a proved equivalence and failure to find a counterexample.

## Realisation theory as a structural reconstruction precedent

[Mihály Petreczky, Laurent Bako and Jan H. van Schuppen, Realization theory of discrete-time linear switched systems](https://arxiv.org/pdf/1103.1343), §§2–5, especially Theorem 5, PDF p. 12.

**Already supplied.** The paper gives existence and minimality criteria, minimalisation procedures and construction of a state-space system from input-output behaviour. In its switched setting, realisability requires a generalised convolution representation and finite rank of a generalised Hankel matrix. The constructed minimal state's dimension is the Hankel rank. Minimality is characterised by span-reachability and observability; minimal realisations of the same behaviour are isomorphic.

**Conditions and boundary.** The system class and switching-input interpretation are specified. Exact full behaviour, or enough exact information satisfying the finite reconstruction conditions, is stronger than arbitrary noisy observations. Minimal realisation recovers a behavioural representative within the class, not every hidden implementation detail. The generalised convolution condition must not be dropped when quoting the finite-rank criterion.

**Implication.** Recovering a compact structure from composable experiments, or interpreting rows/columns as reachability and observation, has direct nontrivial precedents.

An older categorical comparator is [Arbib and Manes, Generalized Hankel Matrices and System Realization](https://epubs.siam.org/doi/abs/10.1137/0511038). Its primary publisher abstract already states realizability, partial/canonical realisation and categorical dimension results for generalised Hankel data. This abstract-level check is enough to reject a blanket claim that categorical realisation has been missing, but not enough for a theorem-by-theorem novelty verdict.

## Falsifiable targets for an ambitious contract

These are proposed research obligations, not claims that the literature has left them open. Selecting one requires a further search for its closest technical predecessors.

### Generate explanatory structure under explicit experimental access

Specify the model class, permissible probes and interventions, composition operations, observation values, noise assumptions and resources. Construct an algorithm that returns both a candidate structured model and evidence for the claimed relationship to the observations. State which parts of the structure are learned and which are supplied as grammar, priors or semantics. Require a nontrivial theorem giving conditions for soundness, identification up to a stated equivalence, or a certified failure of identification. A recovery result that only redescribes an existing minimal-realisation theorem is a baseline, not the promised advance.

The central impossibility test is simple: if two permitted systems yield the same permitted observations, the procedure cannot claim to distinguish their hidden structures without extra assumptions or new experiments. Make that an explicit negative control. Where identification is impossible, return an ambiguity class or a distinguishing experiment that becomes available under a clearly stated extension of access.

### Make inferred structure survive composition and changes of tests

State an operational property stronger than agreement on isolated observations. For example, learned correspondences might have to predict unobserved compositions or transport an intervention across levels with an explicit error bound. Prove the hypotheses under which this extends from generators to composite experiments, and exhibit a counterexample when a required hypothesis is absent. If changing probes merges previously separated states or destroys a mechanistic lifting, the procedure should expose that consequence rather than report an unexplained similarity change.

This target succeeds only if the theorem or algorithm changes what can be inferred, computed or tested. Merely drawing a commuting square for a previously known relation does not satisfy it.

### Discover and validate mechanisms before the outcome is known

On a controlled neural-learning benchmark, infer a structured candidate explanation using only information available before a declared training cutoff. Keep the final checkpoint and evaluation interventions hidden during discovery. Test the explanation's predictions on unseen training runs and interventions, and compare with ordinary losses, spectral summaries and existing mechanistic analyses. Predeclare what constitutes improvement: prediction error, intervention accuracy, computational cost or experimental sample use. Include cases with equivalent task behaviour but different internal mechanisms.

An ambitious success would combine a reusable discovery procedure, a mathematical account of when its output deserves its structural interpretation, and successful out-of-sample causal predictions. A negative result that precisely identifies which probes or assumptions are insufficient is also substantive. Success on a reproduced circuit alone, or a post hoc metric tuned after the transition, does not meet this target.

### Set a novelty and stopping rule

For each proposed theorem or algorithm, identify the closest existing result and list the exact change in inputs, assumptions, conclusion or computational guarantee. If the construction reduces to the predecessor without a new consequence, retain it as exposition and revise the research claim. If the designated benchmark cannot separate the new method from its baselines, revise the benchmark before interpreting a numerical win as structural discovery. Do not promise universal identification across arbitrary systems from finite observations.
