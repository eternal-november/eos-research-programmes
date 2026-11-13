# Joint native realization: strongest-source audit

2026-11-03. Scope: finite local realization witnesses, overlapping interfaces, compatibility, resources and coherent assembly. This is a bounded primary-source audit, not novelty clearance.

## Preliminary verdict

Several natural versions of the proposed problem already have strong general solutions. Overlap-consistent distributions on acyclic covers glue by classical marginal-extension theory. Conditional-independent gluing is the Markov combination. This remains true when local latent variables are included among the coordinates. Deterministic transition-preserving shared interfaces admit semipullbacks of Markov processes, so merely replacing marginal tables by local transition mechanisms does not create a new gap. Boolean/probabilistic global extension and their support comparison are already unified by semiring-valued contextuality.

The more discriminating target is preservation of specified *stochastic* comparison maps and factorization witnesses, especially with a shared latent budget or joint constraints not determined by local marginals. Any positive theorem should say exactly whether it preserves local joint laws, conditional response kernels, transition morphisms, chosen factorization objects, or a prescribed joint coupling. These are different obligations. Retaining hidden variables in a table can preserve a joint law without preserving every mechanistic or intervention interpretation.

## 1. Marginal extension and acyclic covers

N. N. Vorob'ev, **Consistent Families of Measures and Their Extensions** (1962), Theory of Probability and its Applications 7(2), 147–163. DOI https://doi.org/10.1137/1107014 ; original publisher/archive record with theorem statement: https://www.mathnet.ru/php/archive.phtml?jrnid=tvp&option_lang=eng&paperid=4710&wshow=paper .

The original abstract characterizes the complexes for which every consistent family of measures extends, using its regularity condition. Acyclic hypergraph formulations are standard descendants. This settles a structural sufficient condition on the overlap pattern rather than assuming a joint measure. It also shows why pairwise consistency alone fails on general covers. We verified the original record's theorem statement, not the full Russian proof; do not assign an unverified theorem number or equate every modern notion of hypergraph acyclicity without a translation proof.

**Application to this task.** If mechanism preservation means retaining fixed local joint distributions on observables and named local hidden coordinates, their global extension remains a marginal problem on the enlarged coordinate cover. Enlarging a tree cover can change its overlap pattern; this must be checked, not presumed.

## 2. Conditional products already unify probability and relations

A. P. Dawid and M. Studený, **Conditional Products: An Alternative Approach to Conditional Independence**, AISTATS 1999, pp.27–35. Primary full text: https://proceedings.mlr.press/r2/dawid99a/dawid99a.pdf ; bibliographic record https://proceedings.mlr.press/r2/dawid99a.html .

Section 2 axiomatizes projection and a partially defined conditional product; weak compatibility is agreement of projections, while strong compatibility means existence of an extension. Observation 2.1 derives preservation of the original factors. Section 3 develops probability products, including measurable-space qualifications; Section 4 gives a set-theoretic version related to variation independence and relational databases. The paper also exhibits settings where the desired product does not exist. Its axioms include compatibility with restriction and staged assembly. Thus an abstract common gluing operation for relations and probability is established prior art, not a new consequence of renaming the objects.

**Application.** In finite probability, for two consistent marginals p_A and p_B, their conditionally independent combination is p_A p_B / p_{A∩B}, with zero convention on zero-overlap mass. The scope of associativity must be explicit: shared-boundary or running-intersection assemblies have the expected law; arbitrary overlapping cyclic merges cannot be advertised as unconditionally associative while preserving all original marginals.

## 3. Model combination preserves local conditional models too

R. J. B. Goudie, A. M. Presanis, D. Lunn, D. De Angelis and L. Wernisch, **Joining and splitting models with Markov melding**, Bayesian Analysis, DOI https://doi.org/10.1214/18-BA1104 ; author manuscript https://arxiv.org/abs/1607.06779 ; primary full article https://pmc.ncbi.nlm.nih.gov/articles/PMC6324725/ .

Section 3.1 recalls Markov combination of submodels with a common link-parameter marginal: multiply the conditionals given the link parameter and its common marginal. It preserves each submodel's prior joint law and link-conditional law, while imposing conditional independence between the submodels. If link marginals disagree, Markov melding explicitly replaces them by a pooled marginal before combining. That is a model modification, not exact preservation. The article emphasizes that posterior submodel marginals are not generally preserved after all data are incorporated.

**Application.** A proposal to combine fixed local latent emission models over a common latent interface can fall directly within this construction. Extra importance assigned to the word “mechanism” does not by itself take the theorem outside existing model combination. Conversely pooled replacement is not an acceptable proof of exact witness-preserving compatibility.

## 4. Categorical global extension over Boolean and probability coefficients

S. Abramsky and A. Brandenburger, **The Sheaf-Theoretic Structure of Non-Locality and Contextuality**, New Journal of Physics 13 (2011), 113036. Primary full text https://arxiv.org/pdf/1102.0264 .

Section 2.3 defines finitely supported normalized distributions over a commutative semiring, explicitly including Boolean and nonnegative-real coefficients. Section 4.3 writes global-extension constraints as one incidence-matrix system. Proposition 4.4 uses the support semiring homomorphism to send probabilistic solutions to Boolean ones, and explains why the converse fails. Theorem 8.1 identifies factorizable hidden-variable realizability with existence of a global distribution section. These are directly relevant common-construction and independent-feasibility controls.

**Boundary.** Global hidden-variable realizability does not automatically retain a *chosen* factorization of each local table, its exact latent cardinality, or a preassigned stochastic simulation between hidden carriers. The theorem gives existence in its native class, not a canonical optimizer or arbitrary physical mechanism reconstruction. The note's local witness requirements must be compared to these distinctions precisely.

## 5. General agreement and disagreement machinery

S. Abramsky and G. Carù, **Non-locality, contextuality and valuation algebras: a general theory of disagreement** (2019). Primary full text https://arxiv.org/pdf/1911.03521 .

Section 4 views local agreement as compatible sections and global agreement as extension. Theorem 4.1 recovers contextuality as global disagreement of a locally agreeing knowledgebase. Section 5 defines adjoint valuation algebras: combination is right adjoint to paired restrictions; Proposition 5.1 connects global agreement to combining and projecting. The source explicitly distinguishes restriction-presheaf structure from the extra combination operation. Its examples include relational databases, constraint satisfaction and logical systems.

**Application.** A categorical packaging of overlap consistency, obstruction and relational natural joins must be assessed against this broader existing framework. Merely supplying a presheaf or adjunction does not establish native stochastic realization or budget preservation.

## 6. Transition mechanisms and deterministic shared quotients

A. Edalat, **Semi-pullbacks and bisimulation in categories of Markov processes**, Mathematical Structures in Computer Science 9(5), 523–543 (1999), DOI https://doi.org/10.1017/S0960129599002819 . Publisher primary abstract: https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/semipullbacks-and-bisimulation-in-categories-of-markov-processes/E6B376BF5177E57A39200F9806351D4C .

The abstract establishes semipullbacks for families of Markov processes on Polish spaces with transition-preserving surjective continuous maps, and related categories with analytic spaces and Borel maps. A shared quotient cospan can therefore be completed by a common process whose projections preserve transitions. This is stronger than merely matching static distributions. We verified the publisher abstract, not the full original proof.

J. Pachl and P. Sánchez Terraf, **Semipullbacks of labelled Markov processes**, Logical Methods in Computer Science 17(2:3), 2021. Primary full text https://arxiv.org/pdf/1706.02801 ; DOI https://doi.org/10.23638/LMCS-17(2:3)2021 .

Theorem 2.2 constructs semipullbacks of Radon subprobability kernels over a fixed measurable source, with carrier the set-theoretic pullback. Theorem 5.1 obtains the corresponding labelled-Markov-process result; Theorem 5.3 extends to separable universally measurable spaces. Morphisms are surjective measurable *functions* preserving kernels, not arbitrary stochastic maps. Their introduction carefully distinguishes span-defined bisimilarity from cospan-defined behavioral equivalence.

**Application.** Finite deterministic quotient gluing is a very special instance. Its product/fibre-product state bound is available directly. A semipullback is not a categorical pullback with a unique universal mediating map, nor does the existence theorem itself choose a coherent optimizer. Arbitrary stochastic interface links, additional forbidden joint states, or minimum-cardinality common covers need separate treatment.

## 7. Resource costs are not supplied by maximum-entropy gluing

M. Kocaoglu, A. G. Dimakis, S. Vishwanath and B. Hassibi, **Entropic Causality and Greedy Minimum Entropy Coupling** (2017), https://arxiv.org/abs/1701.08254 ; S. Compton et al., **Minimum-Entropy Coupling Approximation Guarantees Beyond the Majorization Barrier**, AISTATS 2023, primary https://proceedings.mlr.press/v206/compton23a.html .

These study joint distributions with fixed marginals while minimizing entropy, including algorithmic hardness and approximation. They are a useful warning that feasible gluing, a conditionally independent glue, and resource-optimal gluing are different tasks. Entropy is not latent cardinality, so these results must not be cited as a hardness theorem for the latter without a reduction.

## 8. Focused follow-up: fixed-kernel and multicausal couplings

The developed formulation uses nonnegative joint masses Z(j,h,s), first-stage masses alpha(j,h), and constraints whose local s_i marginals equal alpha(j,h) B_i(h_i,s_i). On every positive-alpha fibre this says exactly that the conditional joint response beta(j,h,·) is a coupling of the prescribed local response laws B_i(h_i,·). This is established conditional-kernel coupling structure; preserving these mechanisms is not by itself an uncovered problem.

Kevin O'Connor, Kevin McGoff and Andrew B. Nobel, **Optimal Transport for Stationary Markov Chains via Policy Iteration**, JMLR 23(45), 2022. Primary full text https://www.jmlr.org/papers/volume23/21-0519/21-0519.pdf . Definition 2 requires each row of a joint transition matrix to couple the corresponding prescribed local transition rows. The authors explicitly identify the linearity of these constraints as a computational advantage. Definition 3 extends this to stationary process couplings. Their optimization concerns transport cost, not latent-cardinality minimization. The present finite response problem is not stationary, but its per-fibre kernel condition is the same construction.

Vrettos Moulos, **Bicausal Optimal Transport for Markov Chains via Dynamic Programming** (2020). Primary full text https://arxiv.org/pdf/2010.06831 . Section 2, equations (8)–(9), defines the same fixed-marginal joint kernel and builds its path law. The paper relates this to bicausal transport and derives dynamic programming and optimal Markovian couplings for its cost setting. This establishes that preserving local next-step behavior after conditioning on the joint past is already a central, explicit requirement in coupling theory, stronger than static marginal agreement.

Beatrice Acciaio, Daniel Kršek and Gudmund Pammer, **Multicausal transport: barycenters and dynamic matching**, SIAM Journal on Financial Mathematics 16(3), 1104–1138 (2025). Primary author manuscript https://arxiv.org/pdf/2401.12748 ; DOI https://doi.org/10.1137/24M1634096 . Lemma A.3 characterizes multicausal couplings by successive joint kernels having the prescribed local conditional marginals; Remark A.4 gives the converse construction. Lemma A.5 preserves multicausality when gluing over a shared process. Lemma A.6 simultaneously retains prescribed bicausal pair couplings through one common process. These results are particularly close to the intended mechanism-preserving assembly and must be cited, rather than treating multicomponent kernel gluing as unexplored.

**Precise reduction and residual scope.** With all local kernels fixed, substituting Z=alpha beta and summing out unwanted coordinates turns conditional marginal equations into linear constraints in (alpha,Z). This is the finite joint-mass representation of conditional coupling. Additional observable-table or forbidden-support requirements impose linear slices. Feasibility duals then come from ordinary linear programming; zero-alpha fibres require a stated convention or removal. Conversely finite disintegration recovers beta from feasible Z on positive fibres. This reduction is a substantive check of the specified model but not a new general coupling principle.

The present notion can be compared directly with two-time multicausal coupling once the time-zero variables and any public j are included in each appropriate local filtration. The equivalence should be written down with those histories: conditioning on an external public input that is absent from a source's filtration is not automatically the identical definition. There is no need to claim full multicausal transport equivalence when only the per-fibre coupling construction is used.

Finite splitting/conditioning comparison maps and any initial object derived from conditional laws should likewise be described as a categorical organization of these calculations unless an additional universal property is proved. A support-minimum or latent-factor minimum is not the transport-cost objective above. Exact preservation of given factors and cardinality, if established, remains a separately specified resource theorem; the cited coupling results should not be credited with that theorem without a reduction, but absence of the same resource statement here does not establish novelty.

## Decision rules for the proposed theorem

1. Specify fixed data before writing a gluing theorem: local tables, latent factors, comparison maps, transition operators, interface equations, forbidden support, and resource type.
2. If all conditions are fixed linear marginals on an explicitly finite joint carrier, compatibility is a polytope feasibility problem with Farkas/separation certificates. A dual inequality is an actual independent test but its generic existence is standard linear programming.
3. If maps to the shared interface are deterministic transition morphisms, first reduce to semipullbacks. A finite proof may be valuable exposition, not evidence of a missing general theorem.
4. If all local latent joint distributions can be placed on a running-intersection cover, test ordinary Markov combination before claiming a mechanism-preserving advance.
5. If the result must retain *stochastic* factorization maps, fixed-size common factors or additional joint conditional constraints, record explicitly which established reduction fails. This is the most plausible place for a meaningful additional theorem in the current finite setting.
6. Do not infer arbitrary associativity from binary existence. Either choose a canonical conditional-independent assembly on a controlled cover, retain all possible joint witnesses with restriction comparisons, or prove a new coherent selection theorem.
7. Distinguish support size, Boolean rank, nonnegative rank and entropy. Their minima need not agree, and marginal consistency does not preserve chosen optimal factors.

## Audit limits

No exhaustive citation-network or all-language search was performed. No source identified here proves the proposed exact fixed-factor, fixed-resource theorem in full generality. That is not evidence that such a theorem is absent. The immediate lesson is that the easiest marginal, deterministic-mechanism, and common Boolean/probabilistic versions already have substantial theory behind them. The next manuscript should make its reduction to these sources explicit, then isolate any added constraint and prove the corresponding additional law rather than treating a standard gluing result as a new theory of phenomenology.
