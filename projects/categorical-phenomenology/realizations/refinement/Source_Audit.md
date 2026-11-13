# Native observation refinement: focused reduction audit

Date: 2026-11-02. This is a bounded primary-source audit, not a claim of exhaustive novelty clearance.

## Bottom line

The proposed finite controlled stochastic test is largely covered by established mathematics once its comparison is fixed. Labelled stochastic intertwinings already express preservation of initial preparations and joint output/transition kernels. Deterministic versions are strong lumpability. Exact bounded-size synthesis reduces to existential real algebra using a standard finite certificate for weighted-language equality. Requiring projection to two *fixed* models is a different, stronger problem: supported Markov couplings solve it with a product-state bound. None of these automatically turns trace equivalence into a prescribed state comparison.

The early/late randomness example is an especially good negative control, but its underlying distinction is established prior art, not a new obstruction principle.

## Verified primary sources and exact scope

### 1. Kiefer–Wachter: bounded native realization via real algebra

Stefan Kiefer and Björn Wachter, *Stability and Complexity of Minimising Probabilistic Automata* (ICALP 2014), §4.2, Proposition 10 and Theorem 11. Author manuscript: https://arxiv.org/pdf/1404.6673 .

For rational input automata, they give a polynomial-size existential-real encoding of an equivalent automaton of prescribed size; coefficients in the sought automaton may be real. The equivalence certificate is an invariant row space in the direct sum of the two representations, containing their initial row and annihilating the difference of final columns. This avoids asserting equality for infinitely many words. They establish NP-hardness of native probabilistic minimization and a PSPACE upper bound, rather than an efficient optimizer. Their fixed-initial semantics is explicitly distinguished from stochastic sequential machines with varying preparations (§1). Do not quote their historical rationality question as still open without a fresh audit.

**Our reduction, not a theorem quoted verbatim:** encode action/output pairs as letters; retain per-action stochastic normalization. Add one certificate per supplied preparation, and add the chosen-model comparison equations below. This leaves a finite polynomial system. Polynomial size is in the requested state dimension (e.g. unary budget); a binary exponentially large budget needs separate complexity accounting.

### 2. Ésik–Maletti: exact comparison is an existing simulation matrix

Zoltán Ésik and Andreas Maletti, *Simulation vs. Equivalence* (2010), Definition 3.1: https://www.informatik.uni-leipzig.de/~maletti/pub/esimal10.pdf .

Their row-vector simulation A→B is a matrix X satisfying αX=γ, M_a X=X N_a for every letter, and β=Xδ. Consequently all word weights agree. For terminal columns of ones, a nonnegative such X is row-stochastic. Thus our proposed stochastic comparison is a normalized instance of this established notion, after aggregating fine outputs to coarse outputs. Their common-span theorem for Noetherian semirings must **not** be silently applied to the nonnegative reals: real-vector-space spans can contain negative coefficients and need not be native stochastic systems. A zigzag is also not one specified arrow to a chosen coarse model.

### 3. Bian–Abate: the negative control already has the same structure

Gaoang Bian and Alessandro Abate, *On the Relationship between Bisimulation and Trace Equivalence in an Approximate Probabilistic Context* (2017), Figure 1 and accompanying text: https://arxiv.org/pdf/1701.04547 .

Their figure contrasts early and late resolution of a fair branch: both initial states produce the same aab/aac traces, yet their branching-time conditional probabilities differ. This directly controls the conceptual novelty of our delayed-randomness example. Adding a fine first output that exposes the future branch makes the incompatibility with a chosen late-randomness implementation visible. Proving impossibility for every rich realization admitting a given stochastic-link direction is an adapted argument, not something the figure itself states.

### 4. Supported couplings: fixed-pair common refinements

Bengt Jonsson and Kim G. Larsen, *Specification and Refinement of Probabilistic Processes*, LICS 1991, pp.266–277: https://lics.siglog.org/1991/JonssonLarsen-Specificationandref.html . The official abstract distinguishes structural satisfaction from inclusion of implementation sets. The exact coupling formulation of their Definition 4.3 / Theorem 4.6 is reproduced and attributed in S. Z. Fatmi, S. Kiefer, D. Parker, F. van Breugel, *Robust Probabilistic Bisimilarity for Labelled Markov Chains*, §2 Definition 1: https://arxiv.org/pdf/2505.15290 .

There a related pair has equal labels and a coupling of its successor laws supported on the relation; for equivalence relations this equals the usual class-mass formulation. Selecting such couplings constructs a product-state Markov chain. Applying this separately to each action, with fine outputs and their coarse images matched, gives the corresponding joint-kernel construction. The product bound and initial-coupling check are immediate finite specializations. They establish a common refinement of two fixed models, not the least size among arbitrary models realizing the richer behavior.

### 5. Positive realization: essential baseline, not the anchor by itself

Heller's invariant-polyhedral-cone criterion is classical. A carefully stated account including the correction to the original proof is Boyle–Petersen, *Hidden Markov Processes in the Context of Symbolic Dynamics*, Theorem 4.40: https://math.umd.edu/~mboyle/papers/BoylePetersen07-10-2009.pdf . Original references: Heller, *On stochastic processes derived from Markov chains* (1965), DOI 10.1214/aoms/1177700000; *Probabilistic automata and stochastic transformations* (1967), Math. Systems Theory 1:197–208. Primary complementary treatment: Michel Fliess, *Séries rationnelles positives et processus stochastiques* (1975), https://www.numdam.org/article/AIHPB_1975__11_1_1_0.pdf .

The invariant cone distinguishes finite nonnegative realization from mere finite linear rank. An unconstrained realization criterion does not itself preserve a prescribed coarse state presentation. An anchored cone characterization would need the state-comparison data and its intertwining constraints, not merely a cone with the right observable image. The supplied sources do not justify claiming such an anchored formulation new.

## Explicit reduction to test, with directions fixed

Take coarse matrices C[a,y] on n states, fine candidates X[a,z] on k states, output garbling g:Z→Y, and row-stochastic L:k→n. Let Xbar[a,y]=sum_{g(z)=y} X[a,z]. Require:

- all X[a,z]≥0 and sum_z X[a,z]1=1, for each action a;
- each required fine initial row μ_i satisfies μ_i L=ν_i;
- Xbar[a,y] L=L C[a,y], for every a,y;
- exact richer behavior, enforced by the invariant-subspace certificate against its supplied finite weighted representation.

All are polynomial equalities/inequalities. Deterministic L is expressible by entries satisfying L_ij²=L_ij plus row normalization; surjectivity, if requested, is another finite constraint. Stochastic output garbling is handled by replacing the fibre sum with weighted sums. This is bounded *feasibility*, not automatically practical or a closed-form optimal resource bound.

Initial rows and labelled kernels imply coarse trace preservation by induction. Merely checking sum_y kernels is insufficient: it can forget output/next-state correlation. The opposite-direction stochastic link is a genuinely different property and must not be substituted.

## Stopping boundary / conclusions warranted

1. For fixed supplied finite behavior representation and fixed state budget, complete existence testing reduces to known real-algebra machinery, with elementary additional anchor constraints.
2. Trying budgets computes the minimum on positive instances once existence is known; without an a priori bound or a separate obstruction theorem, endless failure at finite budgets is not an unbounded nonexistence decision procedure.
3. A fixed fine realization jointly coupled to the coarse realization has a standard product construction when the supported-coupling relation and initial coupling exist. Its failure does not rule out *another* realization of the same fine behavior.
4. Hankel rank and finite-table nonnegative rank yield lower bounds, but native sequential feasibility also requires all continuation operators. A response-matrix factorization alone loses precisely this requirement.
5. No new general theory is warranted merely by restating these reductions. Any subsequent target should make a useful demand these reductions do not already deliver: a sharp anchored resource theorem, a genuinely effective unbounded criterion in a stated class, or a substantive observation-change transport law. Their absence from this short audit is not evidence of novelty.

## Additional verified coefficient boundary

Chistikov, Kiefer, Marušić, Shirmohammadi and Worrell, *On Rationality of Nonnegative Matrix Factorization* (SODA 2017), §5, proves that minimizing labelled Markov chains can require irrational transition probabilities even from rational inputs: https://wrap.warwick.ac.uk/97743/7/WRAP-rationality-nonnegative-matrix-factorization-Chistikov-2017.pdf . Therefore real-algebra feasibility must not be replaced with enumeration of rational candidate probabilities. The coefficient domain must be stated explicitly. This is an established obstacle, not a new finding of our reduction test.

## Two-stage test fully reduces to Blackwell comparison

Fix positive latent weights w_s, stochastic future rows Q_si, and desired joint signal/future law R_ji with the same future marginal μ_i=Σ_s w_sQ_si=Σ_j R_ji. The candidate feasibility condition is K_js≥0, Σ_jK_js=w_s, and KQ=R. On μ_i>0 define stochastic experiments D_is=w_sQ_si/μ_i and E_ij=R_ji/μ_i. Then set L_sj=K_js/w_s. Direct substitution gives

(DL)_ij = Σ_s(w_sQ_si/μ_i)(K_js/w_s) = (KQ)_ji/μ_i = E_ij.

Conversely E=DL with L stochastic gives K_js=w_sL_sj and both original constraints. If μ_i=0, nonnegativity and w_s>0 imply every Q_si and R_ji is zero; delete those future outcomes. Thus feasibility is **exactly** garbling D→E: the chosen latent signal S must dominate the proposed early signal J as an experiment about the future outcome I. The joint implementation P(i,s,j)=w_sQ_siL_sj has J conditionally independent of I given S. This is a statement about existence of a compatible joint law, not about conditional independence in an arbitrary pre-existing coupling of S and J.

Primary source directly matching the categorical formulation: Fritz, Gonda, Perrone and Rischel, *Representable Markov Categories and Comparison of Statistical Experiments in Categorical Probability*, arXiv:2010.07416v3 (2023), §5.1 and Theorem 5.4, https://arxiv.org/pdf/2010.07416 . That theorem characterizes garbling through sufficient joint implementations and conditional independence. It requires conditionals, not representability. FinStoch has conditionals but is explicitly **not** representable; do not apply the later representable-category theorem directly to FinStoch. Classical historical reference: Blackwell, *Equivalent Comparisons of Experiments* (1953), DOI https://doi.org/10.1214/aoms/1177729032 . The matrix reduction itself needs only the standard garbling definition, not the full decision-theoretic Blackwell theorem.

Consequently the two-stage LP is a genuine complete reduction to existing experiment comparison, not evidence for a new general phenomenon. The constrained minimum-size problem and arbitrary multi-stage anchored realization remain distinct.
