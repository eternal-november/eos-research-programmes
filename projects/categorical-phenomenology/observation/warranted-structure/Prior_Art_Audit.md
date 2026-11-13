# Prior-art audit: structure reconstructed from evidence and tests

Research date: 2026-11-03. Primary papers were inspected through their full-text sources unless explicitly marked otherwise. This is a targeted comparison, not an exhaustive novelty search. Mathematical deductions below are identified separately from source claims.

## Main assessment

The broad claim that existing mathematics only accepts a finished structure and does not reconstruct structure from observation is untenable. Strong counterexamples include active automata learning, categorical automata learning, causal-state reconstruction, predictive-state discovery, attribute exploration, and learning algebraic isomorphism types from informants.

A narrower contribution might concern the simultaneous revision of the empirical carrier, admissible observations, operational vocabulary, and structural commitments, with explicit comparison maps and finite-evidence warrant. That is a research specification, not yet a demonstrated novelty result. Merely allowing additional observations, additional tests within a fixed grammar, unknown state counts, or revised hypotheses is already well established.

Crucial distinction: an unknown target may appear in a theorem's semantics without being supplied to the learner. A categorical diagram containing a target object is not evidence that the algorithm receives that object's carrier or transitions.

## A. Strongest primary precedents

### 1. Angluin, *Learning Regular Sets from Queries and Counterexamples* (1987)

[Full paper](https://people.eecs.berkeley.edu/~dawnsong/teaching/s10/papers/angluin87.pdf), Information and Computation 75, 87–106.

Sections 2.1–2.2, pp.90–97: an observation table has prefix representatives S, suffix experiments E, and queried outcomes T. Its rows become hypothesized states. Both S and E grow. New experiments split formerly identical rows. Closedness supplies representatives for successor rows; consistency ensures equal rows have equal successor rows. Theorem 1 gives a minimality result among acceptors consistent with the finite table; Theorem 6 identifies the target's minimum DFA up to isomorphism.

Fixed prerequisites: a known finite alphabet, a regular target, exact membership answers, and equivalence queries returning counterexamples. Section 4 replaces equivalence queries with random examples for approximate, high-probability learning, not the same exact guarantee.

Comparison: state carriers, transitions, and discriminating experiments are inferred, not supplied. Test syntax remains words over a fixed alphabet. The observed equal-row relation is refined by adding columns. This is a direct predecessor of finite-evidence quotients and the same-level transition-descent condition.

### 2. van Heerdt, Sammartino, Silva, *CALF: Categorical Automata Learning Framework* (2017)

[Full paper](https://arxiv.org/html/1704.05676), CSL 2017.

Section 3 introduces a wrapper S → T → P around an unknown target and factors its composite as S ↠ H ↪ P. H is the hypothesized carrier. Definition 8 formulates closedness and consistency categorically. Theorem 9: for an E-preserving endofunctor F, those conditions are equivalent to existence of the compatible algebra structure FH → H. The examples include deterministic and weighted automata.

Fixed prerequisites: ambient category, factorization system, behavioral/algebraic type, and access assumptions instantiated by a learning algorithm. The target is part of the correctness semantics, not thereby learner-visible.

Comparison: directly counters the assertion that category theory cannot formalize emergence of an algebraic structure from observations. It does not, merely by this theorem, infer an unrestricted new signature or justify the observational interface itself. Its distinction between a hypothesized carrier and a compatible structure is especially close to the proposed issue.

### 3. Vaandrager, Garhewal, Rot, Wißmann, *A New Approach for Active Automata Learning Based on Apartness* (2022)

[Full paper](https://arxiv.org/html/2107.05419).

Sections 2–3 define partial Mealy machines and witnessed apartness. L# begins with a one-state observation tree, extending it with input/output observations and counterexamples. The witnessed-apartness relation grows monotonically. Hypotheses use a discovered basis and map frontier states to compatible basis states. Definition 7 calls a hypothesis consistent when a functional simulation exists from the observation tree to it. Theorems 3.2–3.6 establish identification and complexity under the stated learning model.

Comparison: particularly strong precedent for an evidence structure that grows while inferred identifications remain defeasible. Absence of a distinguishing witness is not established behavioral equality. Fixed prerequisites include input/output alphabets and access to output/equivalence queries. Adaptive distinguishing sequences already make the chosen experiment depend on intermediate results. This is not unrestricted evolution of the action vocabulary.

### 4. Shalizi, Shalizi, Crutchfield, *An Algorithm for Pattern Discovery in Time Series* (2002 preprint)

[Full paper](https://arxiv.org/html/cs/0210025); [institutional record](https://escholarship.org/uc/item/9fz0f94d).

Sections 2–4: causal states identify histories with identical conditional future distributions. CSSR starts with an IID, one-state hypothesis and adds states/transitions when statistical tests require them. It explicitly infers state count and transition architecture. Section 4 studies convergence to the correct causal-state structure.

The stated assumptions include conditional stationarity, finitely many causal states, and a finite synchronizing suffix for each state. Data are symbol sequences over a finite alphabet; inference also uses a maximum history length and significance threshold. Do not read the abstract's architecture-discovery claim as absence of all modeling assumptions. The manuscript is a 2002 preprint whose displayed journal placeholder should not be cited as an actual JMLR publication.

Comparison: unknown architecture reconstructed from data is an explicit objective, not a collateral interpretation. Predictive causal states should not automatically be equated with interventionist causation or ontologically unique mechanisms.

### 5. James and Singh, *Learning and Discovery of Predictive State Representations in Dynamical Systems with Reset* (ICML 2004)

[Conference paper](https://icml.cc/Conferences/2004/proceedings/papers/117.pdf).

Sections 2–3 distinguish discovering core tests from learning update parameters. State is a vector of outcome probabilities for action-observation experiments. The analytic algorithm expands histories/tests, extracts linearly independent rows/columns, and stops when successive ranks agree; its proof assumes exact prediction probabilities. The empirical algorithm estimates those quantities using a reset operation and conservative rank estimation. Section 4 reports cases where sampling finds fewer core tests than the analytic rank.

Comparison: both the representational tests and dynamics can be learned. The ambient action/observation alphabets and linear representation class remain fixed. Empirical stopping is not the exact analytic guarantee.

Bibliographic trap: [Singh et al., ICML 2003](https://cdn.aaai.org/ICML/2003/ICML03-093.pdf), pp.712–713, expressly postpones test discovery and learns predictions for supplied tests. Cite the 2004 work for actual discovery, not the 2003 abstract's decomposition of the problem.

### 6. Bazhenov, Fokina, San Mauro, *Learning Families of Algebraic Structures from Informant* (2020)

[Full paper](https://arxiv.org/html/1905.01601v2); Information and Computation 275, 104590.

Sections 2.2–2.3 fix a signature L, a class of structures on ω, and an effective enumeration interpreting hypotheses. An informant eventually provides every positive and negative atomic fact; functions may be represented by their graphs. A learner maps finite prefixes to conjectures and must eventually stabilize on a correct isomorphism type for every presentation/informant. It need not recognize the stabilization time.

Theorem 3.1 characterizes learnability for the specified family by a sequence of infinitary Σ₂ sentences individually distinguishing its isomorphism types. Corollary 4.1 separately addresses oracle-relative effective bounds.

Comparison: algebraic structure is identified from growing finite evidence, not given to the learner. However, its symbols, arities, candidate family/hypothesis interpretation, and eventual data completeness are prescribed. It does not establish signature discovery or unrestricted learning of arbitrary structures. Avoid silently strengthening the theorem to a computable learner without checking its effectivity hypotheses and the corollary.

### 7. Gehr, Dimitrov, Vechev, *Learning Commutativity Specifications* (CAV 2015)

[Full paper](https://files.sri.inf.ethz.ch/website/papers/cav15-learning.pdf); [authors' publication page](https://www.sri.inf.ethz.ch/publications/gehr2015learning).

Sections 3–5 fix a structure X and a Boolean-closed logical fragment L. The learner queries an unknown relation c, groups samples by logical type, discovers relevant literals, and searches for a concise specification. The commutativity case concerns pairs of already available library operations. Sample size grows until the formula stabilizes.

Scope qualifications: formulas are quantifier-free over finitely many relation symbols. The black box can classify chosen tuples. Relevant-predicate discovery prunes within a supplied language; it is not arbitrary primitive-predicate invention. Section 4.3 explicitly calls the pruning heuristic when logical types are missing. Formula stabilization is an empirical stopping rule, not unrestricted proof of correctness on all unobserved cases. Section 5 discusses observed types becoming ambiguous as additional data arrive.

Comparison: very strong precedent for learning operational laws, including commutativity, from experiments. It is weaker evidence for emergence of the operations themselves or unbounded test-language revision.

### 8. Borchmann and Ganter, *Abstract Attribute Exploration with Partial Object Descriptions* (2015)

[Full paper](https://arxiv.org/html/1511.06191); cite the arXiv submission/version date, not an automatically generated date displayed in the HTML body.

Sections 2–7 separate exploration schema, evolving exploration base, domain expert, and exploration engine. A finite attribute set M is fixed. The engine proposes implications; the expert validates them or supplies partial counterexamples. The base stores established implications and counterexamples, and background knowledge constrains admissibility.

Comparison: structural implication knowledge and admissible attribute combinations are elicited rather than supplied as a completed context. Nevertheless the attribute vocabulary and reliability conditions on the expert are prescribed. Implications characterize the domain only up to intersection closure, as the introduction explicitly notes. This is a useful precedent for evolving evidence and questions, but not for attributing unlimited vocabulary discovery to ordinary attribute exploration.

## B. Finite-depth observation quotients and descent

### 9. Hennessy and Milner, *Algebraic Laws for Nondeterminism and Concurrency* (1985)

[Authors' full text](https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf), JACM 32, 137–161.

Section 2 starts with a process set and atomic observation relations. Theorem 2.2, p.141, characterizes observational equivalence by equality of satisfied modal formulas under image-finiteness. Page 142 explicitly orders equivalences by the power of their formula sets: more formulas distinguish more processes. Page 147 identifies finite-depth approximants with formulas of bounded modal depth. Section 3 distinguishes observational equivalence from the largest congruence it contains, needed for substitution into all program contexts.

Comparison: behavioral identity relative to admissible observations, refinement with observational power, depth approximants, and the extra requirement of operational compatibility are all established. This is primarily a semantics/characterization result, not an algorithm that learns an initially unknown transition system. For nondeterministic systems, matching successors is relational; do not replace it with a single-valued successor map without additional assumptions.

### 10. Dorsch, Milius, Schröder, Wißmann, *Efficient Coalgebraic Partition Refinement* (2017)

[Full paper](https://arxiv.org/html/1705.08362); [proceedings record](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2017.32).

Remark 3.12 gives the final sequence 1 ← H1 ← H²1 ← ⋯ and canonical observations ξ⁽⁰⁾ = !, ξ⁽ⁱ⁺¹⁾ = Hξ⁽ⁱ⁾ ∘ ξ. Its terms represent finite-depth behavior. Proposition 3.7 gives cross-partition maps X/Pᵢ → H(X/Qᵢ). Corollary 3.8 yields a same-carrier quotient coalgebra when Pᵢ = Qᵢ; Theorem 3.10 identifies the simple quotient. Lemma 3.6 establishes refinement of the evidence partitions.

Comparison: especially close prior art for graded observations that do not yet support same-level dynamics. Unlike active learning, this algorithm receives the system to be minimized; its relevance is the formal quotient/compatibility mathematics, not its access model. The functor and assumptions governing the refinement algorithm remain fixed. Do not present the final sequence itself as a new construction.

### Direct mathematical comparison, independently checked

Let X have observation o:X→O and total actions dₐ:X→X, indexed by a fixed alphabet A. Let Eₖ contain observations after words of length at most k, and define x ~ₖ y exactly when all those outcomes agree. Write qₖ:X↠Qₖ=X/~ₖ.

1. Since Eₖ ⊆ Eₖ₊₁, ~ₖ₊₁ ⊆ ~ₖ. The canonical comparison map is pₖ:Qₖ₊₁↠Qₖ, [x]ₖ₊₁↦[x]ₖ. The reverse map is not generally well-defined: an old class may split.
2. x ~ₖ₊₁ y implies dₐx ~ₖ dₐy. Therefore δₐ,ₖ:Qₖ₊₁→Qₖ, [x]ₖ₊₁↦[dₐx]ₖ, is well-defined. This is degree-lowering dynamics, not yet a unary operation Qₖ→Qₖ.
3. A same-level operation d̄ₐ:Qₖ→Qₖ satisfying d̄ₐqₖ=qₖdₐ exists iff x~ₖy implies dₐx~ₖdₐy. Necessity follows by applying d̄ₐ to equal quotient classes. Sufficiency follows by defining d̄ₐ([x]ₖ)=[dₐx]ₖ. Uniqueness follows from qₖ being surjective.
4. In kernel notation, the criterion is ker qₖ ⊆ ker(qₖdₐ). With a general coalgebra ξ:X→HX, it becomes factorization of Hq ∘ ξ through q. For Set this is equivalent to constancy on q-fibres.
5. With H(Y)=O×Yᴬ, the canonical final-sequence cone records exactly these finite observations, up to indexing: its zeroth term is the singleton, whereas Q₀ here already records o. Images of successive cone maps yield a graded system Qₖ₊₁→O×Qₖᴬ. This is a deterministic specialization of the final-sequence mathematics, not an identification of every arbitrary test system with a coalgebraic final sequence.

Noisy, partial, or nonuniformly available tests need extra treatment. Equal outcomes on a common total test set define an equivalence. Merely having no currently recorded conflict need not be transitive. Hypothesis consistency on a finite sample also does not imply that the unknown world's full quotient is a congruence.

## C. Domain growth, implicit determination, and open-world warrant

### 11. Libkin, *Certain Answers as Objects and Knowledge* (2016)

[Author manuscript](https://www.pure.ed.ac.uk/ws/portalfiles/portal/23117001/Libkin_2015_Certain_Answers.pdf), Artificial Intelligence 232, 1–19.

Sections 4–6 treat an incomplete object x through its possible complete realizations [[x]]. Greater information corresponds to fewer possible realizations. Certain answers can be objects, via greatest lower bounds, or knowledge common to all realizations; these need not have equivalent expressive power. Theorem 1 connects knowledge certainty to a greatest lower bound of the common theory. Proposition 8 establishes preservation of informativeness by object-valued certain answers when defined.

Comparison: a strong formal precedent for distinguishing the structure suggested by current observations from conclusions warranted in every compatible completion. Fixed schemas and a chosen realization semantics remain assumptions. Open-world semantics permits additional facts and elements, so a conclusion holding in the currently materialized domain need not be certain.

### 12. Beth definability: qualified relevance

Original reference: E.W. Beth, *On Padoa's Method in the Theory of Definition* (1953), 330–339, DOI 10.1016/S1385-7258(53)50042-3. The original article was not successfully retrieved in this audit.

An inspected primary research comparison is ten Cate, Franconi, Seylan, [*Beth Definability in Expressive Description Logics*](https://ijcai.org/proceedings/2011/188), IJCAI 2011, 1099–1105. Its introduction distinguishes determination of a concept across all models agreeing on a signature from an explicit definition using that signature; its results show that behavior depends on the logic and on finite versus arbitrary models.

Relevance: classical first-order implicit definability concerns uniqueness across all models sharing the reduct, not convergence from finite observations. It does not assert that every experimentally stabilized operation is identifiable, nor that finite-model variants hold automatically. For meets, one need not invoke Beth: the operation's graph already has an explicit order-theoretic first-order definition.

### Domain-expansion counterexample, independently checked

Take the observed four-element diamond P={0,a,b,1}, with a and b incomparable. Its meet a∧b is 0. Add an unobserved c with 0<c<a,b<1. All order relations and nonrelations among the old elements remain unchanged, but the enlarged poset has a∧b=c. Thus even an induced-subposet embedding does not generally preserve meets.

The formula defining z as the meet of x,y is:

z≤x ∧ z≤y ∧ ∀u((u≤x ∧ u≤y) ⇒ u≤z).

The universal quantifier ranges over the ambient domain. A finite observed domain certifies this condition only relative to that domain, unless further completeness/closure assumptions justify it in all compatible extensions. This is not the same phenomenon as quotient refinement by new tests. If a theory already asserts the old element is the meet, then the extension above is excluded by that theory; it is compatible only with the old observed order diagram.

## D. Additional system-identification precedent

### 13. Willems, Rapisarda, Markovsky, De Moor, *A Note on Persistency of Excitation* (2005)

[Authors' institutional abstract](https://ftp.esat.kuleuven.be/stadius/markovsky/abstracts/04-101.html); Systems & Control Letters 54, 325–329; DOI 10.1016/j.sysconle.2004.09.003.

The inspected author abstract states that sufficiently persistently exciting response data from a controllable linear time-invariant system span its finite-window behavior; it also gives conditions for an observed state trajectory to span state space. This is a concrete counterexample to claims that mathematical system structure can only be handed in as a completed model. The assumptions of linearity, time invariance, controllability and informative data are central. Full theorem details were not audited here, so do not import a specific excitation-order formula from this note alone.

## Recommended positioning

1. Treat evidence-induced equivalence, final-sequence depth, quotient descent, and architecture learning as prior machinery.
2. Separate three changes: evidence about a fixed world, extension of admissible tests, and enlargement/revision of the empirical domain. Their comparison maps and monotonicity properties differ.
3. State precisely what is allowed to evolve beyond a fixed signature or behavior functor. Distinguish selecting tests from inventing their grammar.
4. Require a theorem or counterexample about finite-evidence warrant under those changes, or a universal characterization with hypotheses absent from the cited frameworks.
5. Avoid claiming a literature gap from this targeted audit. The defensible result is a map of close precedents and an exact specification of what would still need to be new.
