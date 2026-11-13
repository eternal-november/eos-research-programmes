# Gate A: independent prior-art and reduction audit

Date: 3 November 2026. Scope: the exact claims in `comparative.md` and `learning.md`, including the supplied graph/Gram check script. This is a focused primary-source audit, not a comprehensive novelty certificate. The candidate proofs were inspected independently; finite computations are evidence, not proofs.

## Decision

**Neither candidate is cleared as a new central research theorem.** The learning candidate is the stronger bounded proof seed: its exact sparse-sensor module calculation, optimizer comparison, and sharp graph-dependent jet horizon remain an identifiable additional calculation. The comparative candidate is useful as a quantitative example/control theorem, but its finiteness claim is already subsumed by a much more general decidability result absent from its existing ledger. Its growth exponent is a short virtually abelian orbit-counting argument.

This is not a finding that either full statement has already appeared verbatim. It is a finding that the broad claims of a new reconstruction mechanism, a new finite-state criterion, or a new finite-experiment principle do not survive comparison to the strongest checked sources. Failure to locate the remaining exact specializations is not positive novelty evidence.

## 1. Verified primary statements and their precise use

### 1.1 Bell–Smertnig is stronger than the current comparative finiteness discussion

Jason P. Bell and Daniel Smertnig, *Computing the linear hull: Deciding Deterministic? and Unambiguous? for weighted automata over fields*, LICS 2023; [author PDF](https://math.smertnig.at/paper/linear_hull.pdf), pages 2–3.

**Exact source statement:** Theorem 1 decides whether a weighted automaton over a number field is equivalent to a deterministic automaton, and constructs one when it exists. In its proof, the authors first take a minimal linear representation, compute its reachability linear hull, and use the criterion that all irreducible components of that hull have dimension one. Definition 2 defines the linear Zariski closed sets as finite unions of vector subspaces. Theorem 3/Corollary 6 supply the effective hull computation. The paper explicitly declines a runtime bound and discusses very large output size.

**Use:** after the explicit reduction in Section 2 below, this decides finiteness of exact finite-prefix predictive states for rational controlled response laws with a supplied finite linear realization. Monomial transitions, full-support seeds, and rank-one resets are not needed for that decidability result. This does not give a robust finite-sample test or an efficient general algorithm.

### 1.2 Zhang–Peyré removes the broad Gram and conservation claims

Stephen Y Zhang and Gabriel Peyré, *Global Exponential Convergence of Two-Layer Linear Network Training*, [arXiv:2610.09356v1](https://arxiv.org/html/2610.09356v1), submitted 7 October 2026.

**Exact source statements:** Proposition 2.1, equations (2)–(3), gives covariance closure and indefinite-orthogonal congruence. Definition 2.2 and equation (5) identify the PSD-pencil support interval through signed spectral endpoints; Proposition 2.3 preserves its margins. Appendix D explicitly admits linear losses with constant gradients. Proposition D.1 computes the generated Lie algebra as the indefinite orthogonal algebra. Corollary D.2 identifies generic common smooth conservation laws locally through the signed spectrum. Lemma C.14, equation (42), already quantifies the discrete signature defect.

**Use and limit:** these remove covariance closure, the pencil, its conservation, and Euler's failure to preserve the signature from the novelty budget. The inspected results concern full split controls/conservation, not the exact single-sensor sparse-graph observation module. Conservation completeness is not an observation-equivalence theorem. The paper's convergence assumptions need not hold for the candidate's linear losses; its Appendix D explicitly handles those losses, so that distinction does not rescue novelty of the closure calculation.

### 1.3 Petreczky supplies an exact matrix-word observability predecessor

Mihály Petreczky, *Realization theory for linear and bilinear switched systems: A formal power series approach*, ESAIM: COCV 17 (2011), 446–471; [primary PDF](https://www.numdam.org/item/10.1051/cocv/2010015.pdf), Section 2.3.

**Exact source statements:** Theorem 2.2(ii) identifies two states as indistinguishable exactly when their difference is in the intersection of kernels of all matrix-word output maps. Remark 2.1 states numerical observability and reduction algorithms. Theorem 2.3 characterizes minimal realizations by span-reachability and observability, equivalently Hankel rank, and gives uniqueness up to isomorphism. Theorem 3.1 relates switched/bilinear realization to rational formal-series representations.

**Use:** vectorizing symmetric Grams places the candidate in precisely this finite-dimensional observation-module setting. The finite basis closure and linear solution for the unknown initial response state are applications of that established mechanism. Petreczky does not supply the graph-specific identification of the kernel as span(J), the Euler elimination of that kernel, or the sharp 2d−3 graph horizon in the inspected statements. Those require the candidate's additional calculations.

### 1.4 Token-graph depth is directly supported, with a small boundary qualification

Fabila-Monroy, Flores-Peñaloza, Huemer, Hurtado, Urrutia and Wood, *Token Graphs*, [primary PDF](https://arxiv.org/pdf/0910.4774), Section 3, pages 4–5.

**Exact source statement:** Theorem 1 says that for a connected graph of diameter δ, its k-token graph is connected, with diameter at most kδ and at least k(δ−k+1). Immediately after the proof the paper states that the path attains the latter expression.

**Use:** for d≥3 and k=2, if δ≤d−2 the upper bound is 2d−4; if δ=d−1 the graph is a path and the exact path value is 2d−4. One more collision operation produces the candidate's 2d−3 bound. The d=2 case is checked directly because the paper excludes the degenerate k=n case in its standing setup. The extra sharpness step concerning the first nonzero far-diagonal coefficient is the candidate's elementary matrix-word argument, not a theorem asserted in the token-graph source.

### 1.5 General observation-space construction is already classical

Eduardo Sontag, *Spaces of Observables in Nonlinear Control*, [author PDF](https://sontaglab.org/FTPDIR/icm.pdf), Sections 2–2.1, pages 4–6.

The paper defines the observation space/algebra as the smallest control-invariant linear space/algebra containing the readouts, states canonical algebraic realization and uniqueness, and relates finite-dimensional observation spaces to finite-dimensional affine realizability. This is a direct predecessor for a generic claim that future-response equivalence and update closure produce a learning state. The finite-dimensional linear specialization used here does not require a new general nonlinear realization theorem.

### 1.6 Monomial representation theory is relevant, but ambiguity is a different count

Antoni Puch and Daniel Smertnig, *Factoring through monomial representations: arithmetic characterizations and ambiguity of weighted automata*, [author PDF](https://math.smertnig.at/paper/bezivininvertible.pdf); [arXiv record](https://arxiv.org/abs/2410.03444).

The paper characterizes arithmetic properties of invertible representations through monomial/block-monomial structures, with corresponding weighted-automaton ambiguity classifications and decidability results. Its introductory Remark 1.2 explicitly distinguishes its structural argument from quantitative point counting in related work. Section 11 identifies extension to general noninvertible matrix semigroups as a separate issue.

This is important neighboring structure theory. It is **not** an inspected theorem identifying the number of normalized finite-prefix predictive states. Polynomial ambiguity counts accepting runs for a word, whereas the candidate counts distinct predictive residuals across words. Those quantities cannot be substituted for one another. Likewise, matrix-entry magnitude growth and projective-orbit cardinality growth are different questions.

## 2. Explicit reduction of predictive finiteness to weighted determinization

This section is an independent reduction, not a claim that Bell–Smertnig discuss HMMs in these terms.

Suppose the reconstructed rational row-state model is (α,{A_e},{ℓ_t},u), where α is the designated initial preparation and u is normalization. Include u as one of the terminal effects. Define the scalar rational series on event letters together with terminal letters τ_t by

    f(w τ_t) = α A_w ℓ_t,

and f=0 on strings not consisting of event letters followed by exactly one terminal letter. It has an explicit (k+1)-dimensional representation:

    initial row: (α,0), final column: (0,...,0,1)^T;
    event e: block diagonal (A_e,0);
    terminal τ_t: top-right column ℓ_t, all other blocks zero.

After an event history w of positive probability p_w=α A_w u, its residual series f_w has normalized values

    f_w(v τ_t)/f_w(τ_u) = α A_w A_v ℓ_t / p_w.

Thus two nonzero event-prefix residuals are proportional if and only if they give the same normalized laws for every future protocol and terminal test. The proportionality constant is forced by τ_u; it is positive for genuine nonzero probabilistic histories. Prefixes after termination add only the single line of scalar multiples of the empty-word indicator. Invalid strings add zero. Therefore:

    finite predictive object
    iff finitely many nonzero projective residual series of f
    iff the minimal reachability linear hull of f is a finite union of lines
    iff f has an equivalent deterministic weighted automaton.

Applying the verified theorem decides the condition. Once finiteness is known, a breadth-first enumeration of normalized residual states terminates and yields the predictive transition system. Its outcome probabilities come from the original positive response law; there is no need to assume an arbitrary field-valued deterministic presentation is already a stochastic realization.

**Required qualifications.** Minimize the series for the designated initial preparation, not merely a representation minimal across other preparations. Include all declared terminal tests, or equivalently their effect span, so that hidden distinctions not visible to one scalar output do not inflate the count. Ignore zero-probability histories. The original exact-law/rank promise is still needed to reconstruct the linear realization from finite data; decidability given that realization does not verify the promise from samples. This construction concerns finite prefixes, not stationary infinite-past causal states.

The comparative note may retain its explicit elementary r=0 criterion as a convenient specialized certificate. It should not frame finite predictive-state decidability itself as an unresolved or newly solved HMM problem.

## 3. What remains in the comparative growth calculation

The stated growth proof appears sound under its exact assumptions. Its content is the following elementary chain, rather than a new completion theorem:

1. The projective monomial group has finite permutation image and a diagonal kernel D isomorphic to Z^r.
2. Word balls have O(n^r) elements. Last-reset decomposition reduces all histories to finitely many monomial seed orbits.
3. The semigroup/group gap must be addressed, and the note does address it. If D+ is the positive identity-permutation words, H=<D+> is invariant under conjugation by every generator, since conjugation on diagonal coordinates has finite order. In Γ/H a generator inverse can be replaced by a positive power. A kernel coset therefore has a positive identity-permutation representative, proving H=D.
4. Select r independent positive diagonal loop words. Full support makes their projective action on the initial seed free. Nonnegative products of total bounded length give Ω(n^r) distinct beliefs; observability turns them into distinct response states.

These steps establish Θ(n^r). Rational prime valuations make the diagonal rank effective. The proof does not need an identification of ambiguity growth with state growth, and it does not need a difficult general matrix-semigroup theorem. Whole-control restriction gives a subgroup and cannot increase r.

**Residual status:** no inspected source states the complete monomial/reset predictive-growth theorem in this exact operational form. Nonetheless, its mathematical mechanism is a standard finite-extension/lattice count plus the short semigroup bridge. Its rank can exceed the real dimension of the simplex because it is an arithmetic rank, not a Euclidean dimension. The two-state prime example is valuable for explaining that distinction, but a new terminology such as “holonomy growth” would not create additional mathematical content.

The growth calculation itself survives inspection, but the claimed native realization needs a normalization repair if terminal complements are not already included in the interface. Checking only ℓ_t≥0 on the computed simplex does not check ℓ_t≤u. Require every terminal event and its complement to be nonnegative on the cone, or require each complete terminal-test outcome family to sum to u.

For a concrete failure of the literal incomplete checks, take V=R², u=x_1+x_2, ℓ_1=(3/2)x_1, ℓ_2=(3/2)x_2 as distinguished events of two separate binary tests. Use preparations (2/5,3/5),(3/5,2/5) and scalar event matrices whose outcome weights sum to one. All preparation/history responses are valid and rank two; the computed test-positive cone is the orthant and all monomial checks pass. Yet ℓ_1(e_1)=3/2 at its computed simplex vertex. The derived vertices do not define valid terminal probabilities until complement positivity is checked. This is an input-condition repair, not a failure of the projective growth proof.

The support, observability, at-most-n, and finite-prefix restrictions remain indispensable. With terminal normalization repaired, this is a reasonable worked comparison theorem, not presently a justified flagship novelty claim.

## 4. What remains in the sparse learning calculation

The independent proof inspection supports the central module statements. The native-width formulation needs the d=2 exception stated below:

* Flow closure is the cyclic linear module generated by the sensor under T_e(Q)=S_eQ+QS_e. Token moves produce all off-diagonal Q_ij. Edge collisions produce D_i+D_j. Connected bipartite incidence has a one-dimensional annihilator, giving exactly J-perp.
* The path lower bound 2d−3 counts individual index moves before D_d can appear. All coefficients in the selected construction are nonnegative, so the exhibited far-diagonal term cannot cancel. The pair 0,D_d is PSD and physically realizable, so this is an actual response distinction.
* For a fixed 0<η<1, the six possible eigenvalues of P_e(Q)=(I−ηS_e)Q(I−ηS_e) are strictly ordered:

      (1−η)^2 < 1−η < 1−η² < 1 < 1+η < (1+η)^2.

  Hence spectral interpolation really does recover T_e as a polynomial in P_e, even though T_e has a repeated zero eigenvalue. Then R_e(Q)=S_eQS_e is also a polynomial. Applying R_jk to D_i+D_j yields D_k for adjacent edges. This fills the missing direction for d≥3. For d=2 the invisible line is preserved instead.
* The explicit two-step witness, controls 23 then 12, gives sensor difference −cη³ from initial difference cJ. This proves failure of update descent, not merely drift of a conserved function.
* Fixed positive flow duration τ=log 2 gives L_e=I+(1/4)S_e²−(3/4)S_e. The exponential has distinct eigenvalues on the five T_e eigenspaces, so the endpoint-pullback module is exactly the derivative module. All endpoint matrices are rational.

### Finite identification is an application, not an independent general novelty

Let M be the computed observation-space dimension. Starting from one nonzero sensor, keep independent word images until the span is invariant. Every non-stationary stage increases dimension, so M scalar endpoint experiments with maximum word length M−1 suffice. Here M=D−1 for flow, M=D for GD when d≥3, and M=D−1 for both at d=2. This elementary linear-algebra bound is the finite form of the matrix-word predecessor above.

The special information is the computed value and shape of the module, the fixed-duration/fixed-step interpolation, and the sharper derivative horizon, rather than an abstract claim that finite-dimensional observations admit a finite basis. Reset/replay access and exact observations remain real assumptions. A finite table only identifies the initial state within the declared model class, not the architecture or optimizer from arbitrary black-box data.

### Native-cost claims

The PSD rank factorization and feasible pencil correctly give width compatibility. However, **Theorem C's GD formula needs its d≥3 condition made explicit.** For d=2, GD identifies [Z], not Z, so its minimum response-compatible width is the same feasible-pencil rank minimum as for flow. It cannot be rank(Z) for an arbitrary native representative. For example I_2 and diag(2,0) differ by J, hence give the same d=2 GD response law, while their ranks are 2 and 1.

For the same reason, the d=2 GD-to-flow comparison is the identity on their common quotient, not a map from an identified full Gram. The corrected width conclusions are consequences of the already identified quotient and standard Gram geometry. They are not a new positive-realization theorem. The disconnected maximum-of-component-widths statement is correct because unsensed cross-block Grams may be selected by placing all component factors in a common Euclidean feature space, using the appropriate pencil minimum for every two-vertex component.

**Residual status:** keep the exact graph theorem as an application/proof seed, with unresolved novelty. The source audit supports a strict distinction between what is supplied (two-layer architecture, graph, metric, controls, readout, resets) and what is reconstructed (the observational quotient). It does not support a claim that new representations physically form during training.

## 5. Search coverage and limits

Primary full text was inspected at the exact locations cited above. Searches also covered weighted-automaton projective orbits, monomial semigroup growth, bilinear observability, quadratic outputs, and neural-network weight observability. None of those searches located an explicit statement of the complete sparse-sensor flow/Euler classification.

One adjacent primary result was checked to avoid a false equivalence: Yang, Lopez and Müller, *Local Observability of a Class of Feedforward Neural Networks* ([arXiv:2508.20544](https://arxiv.org/pdf/2508.20544)), uses fixed weights w_{t+1}=w_t, ReLU outputs, and input design with output weights fixed to one. It is not an optimizer-controlled two-factor Gram theorem and cannot be cited as directly subsuming this candidate.

The Hermann–Krener primary PDF was retrieved by the web tool but exposed no readable text, and screenshot extraction failed. No exact theorem numbering is attributed to it here. The Oxford author-manuscript endpoint for the 2025 discretization/unknown-input paper returned HTTP 403; its publisher DOI endpoint was unavailable in the web tool. Their exact statements were not independently reverified in this pass, so this audit does not rely on them for the conclusion. Petreczky and the direct signature-defect source suffice for the relevant reductions.

This pass is not an exhaustive backward/forward citation genealogy, a publication novelty opinion, or a proof-assistant verification. The mathematically responsible outcome is to retain both as explicitly scoped applications, prioritize the learning module if a concrete seed is needed, and leave the contract's new-central-theorem requirement unmet.
