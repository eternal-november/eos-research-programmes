# World learning: when partial experiments justify an explanatory factor

**Status, 2026-11-03.** This is a concrete non-proof test of the categorical-phenomenology program, with complete elementary proofs and computational checks. It is **not a novelty claim**. The generic identifiability boundary is standard marginal/partial-identification linear algebra; the quantitative positive theorem specializes local testing, cut-based design, and sequential change-of-measure. Its value is an explicit, auditable bridge from incomplete observations to a warranted effective structure, including the precise places where that bridge fails.

## 0. Findings worth retaining

1. Identified expectations generally form a vector space, not an algebra. Marginal data can determine two questions separately while leaving their conjunction completely unknown. This does not prevent task-specific linear constructions.
2. That obstruction is data-dependent. Exact deterministic relations in observed pair contexts can collapse the feasible hidden response support and identify the whole response law, even without observing all responses together.
3. There is a robust counterpart with a sharp experiment-interface comparison. A proposed one-bit response factor can be certified against an arbitrary hidden response distribution using local joint contexts. The worst-case complexity is controlled by an explicit fractional cut-hitting LP. For a tree of pair assays it scales as `(m−1)/ε`; for all pair assays as `m/(2ε)`; for all k-response joint assays as `m/(kε)`, with confidence logarithms. These count prepared units/context trials, not individual response measurements.
4. This learns an **operational response factor**, not latent causal coordinates or an intervention on a discovered common cause. It needs a declared same-unit/shared-context measurement contract. Ordinary unpaired interventions do not provide that contract.
5. The affine extension separates two questions exactly: local dual equations must span the full dual code to certify response support; every quotient character must be individually covered to identify the law within that support. Neither condition implies the other. See Section 8.1 and `world_code_extension.md`.
6. The result offers an appropriate methodological target: retain the whole compatible-model set until experiments certify that it lies near a small explanatory model. Do not silently select a conditional-independence or maximum-entropy completion and call it identified.

## 1. A physically meaningful observation contract

Consider a black-box simulator with a reproducible hidden initial state, or a resettable device whose relevant manufacturing type and initial state remain fixed. There are m named stimulus/intervention protocols. Protocol i has a binary response `X_i(U)∈{−1,+1}` for hidden context U. We do **not** assume the protocols compose, correspond to latent variables, or obey any tensor/product decomposition of the physical mechanism.

An allowed context `C⊆[m]` is a set of protocols whose responses can be obtained for the **same** U. A simulator can implement this by making exact snapshots and applying each protocol to a clone. A physical device needs a validated reset/no-disturbance contract; merely repeating a measurement is not enough. The experiment samples a fresh U, returns the whole vector `X_C(U)`, then discards that unit. Its law is the C-marginal of one unknown joint response law μ on `Ω={−1,+1}^m`.

The context family H is an interface specification. A context query costs one independently prepared unit, and `|C|` individual protocol evaluations. Querying a second context on the same unit would be a stronger interface and is not silently allowed.

This contract makes the distinction from ordinary potential outcomes explicit:

- Different people, chips, or independently resampled simulator states under different interventions give only separate marginals.
- Joint responses require a stable shared unit, an exact replay mechanism, or another independently justified coupling.
- Reusing a simulator random seed imposes a particular coupling. The resulting response factor is relative to that declared replay semantics; it is not automatically the unique physical counterfactual coupling.
- An internally stochastic protocol can be represented by adding noise to U only when the observation protocol actually preserves the specified cross-protocol noise coupling. Independent run noise does not become shared noise by notation.

Every joint μ is realizable by a simple finite SCM: draw U in Ω with law μ and set the output of action i equal to U_i. Thus the nonidentifiability examples below are actual hidden-world alternatives, not merely formal inconsistent tables. This SCM representation supplies no claim that U is a physically privileged cause.

## 2. Exact boundary: the compatible-model polytope

For each C and local outcome a, define a cylinder indicator

`l_(C,a)(x)=1{x_C=a}`.

Let L have these indicators as rows, including the normalization row. Given exact observed marginal data b, the compatible joint laws form

`P_b={p∈R^Ω : p≥0, Lp=b}`.

If `P_b` is empty, the shared-response-world contract is contradicted by the data. If it is nonempty, it is a compact polytope. For any bounded target f, the sharp answer is the interval

`[ min_(p∈P_b) f·p , max_(p∈P_b) f·p ]`.

A scalar point answer is justified exactly when this interval collapses. Finite linear programs compute these bounds, but their naive state count is `2^m`, not polynomial in m.

### Proposition 1. Support-sensitive expectation identifiability

Let

`S_b={x : p(x)>0 for some p∈P_b}`.

Then `E_p[f]` is the same for all `p∈P_b` if and only if

`f|_(S_b) ∈ rowspan(L|_(S_b))`.

**Proof.** For every x in S_b choose one feasible p with p(x)>0 and average these finitely many laws. This gives a feasible p° strictly positive on S_b. Every feasible difference lies in `ker L_(S_b)`. Conversely, every vector v in that kernel gives feasible `p°±t v` for sufficiently small positive t; normalization is preserved because it is a row of L. Therefore f is constant on the fiber exactly when it annihilates that kernel, equivalently when its restriction belongs to the row space. ∎

Consequences:

- The joint response law is identified exactly when `rank L_(S_b)=|S_b|`.
- The answer depends both on the experiment family and on observed zero probabilities, which can force S_b to shrink.
- A finite sample never proves a population probability is exactly zero without additional assumptions. The later certificate is deliberately approximate.
- Computing S_b can require up to `|Ω|` linear programs, one maximizing each p(x). A compact constraint representation may be much easier or much harder; it cannot be called efficient just because the final rank test is easy.

This is the standard linear estimability argument expressed at the actual feasible support. It should not be presented as a new categorical theorem.

## 3. Fourier form and the obstruction to unwarranted composition

For `A⊆[m]`, let `χ_A(x)=∏_(i∈A)x_i`, with χ_empty=1. These form the Fourier basis of real functions on Ω. Let

`F={∅}∪{A : A⊆C for some C∈H}`.

The constant is included by normalization, even if no context is available.

When the observed fiber contains a strictly positive joint law, the identified function space is exactly

`V_H=span{χ_A : A∈F}`.

Indeed, the functions on a context C have the basis `{χ_A:A⊆C}`. Hence a target f is identified if and only if every nonzero Fourier coefficient of f has support in F. The affine fiber has dimension `2^m−|F|`.

### Explicit ambiguity witness

If A is not in F, take

`p_±(x)=2^(−m)(1±tχ_A(x)), 0<t≤1`.

Every measured context misses at least one coordinate of A, so summing over the missing coordinate cancels the perturbation. Both laws have identical observed marginals, but `E_±χ_A=±t`. At t<1 both are strictly positive.

In particular, the uniform even-parity and odd-parity worlds have the same marginal on **every proper subset** of coordinates, yet disagree maximally on global parity. More samples of those same contexts cannot resolve the ambiguity.

### The algebra statement, and its limits

Take singleton contexts for two variables. Then

`V=span{1,x_1,x_2}`.

Both x_1 and x_2 are identified, but their product is not. There is no greatest unital pointwise subalgebra contained in V: `span{1,x_1}` and `span{1,x_2}` are both subalgebras, while any subalgebra containing both must contain `x_1x_2`, which is outside V.

More generally, suppose the measured coordinates cover all variables, so V restricted to S_b separates the points of S_b. A unital subalgebra of real functions on a finite set that separates points is the entire function algebra. Therefore:

`identified functions closed under products ⇔ V_b=R^(S_b) ⇔ the full joint response law is identified`.

For the forward implication, separation gives, for any distinct x,y, an f with f(x)≠f(y). Products of normalized separating functions build each point indicator. The reverse implications are immediate.

**This does not block every useful construction.** Expected additive utility, an average treatment effect, or any other target lying in V can be computed without a joint law. A formal algebraic completion is also a legitimate hypothesis language. What fails is treating the expectations of its newly introduced products as facts identified by the original marginal data. A partial multiplication, interval semantics, or the full polytope P_b preserves the distinction.

## 4. Data can remove the obstruction

Suppose observed pair contexts contain the edges of a rooted tree T. For each oriented edge `i→j`, an observed functional relation is

`X_j=g_ij(X_i)` almost surely.

The finite alphabets and functions can be arbitrary. Compose these functions along the unique root paths to obtain `φ_i`, with `φ_r` the identity. Every globally compatible response vector must lie in

`S={φ(z):z∈support(μ_r)}`.

The projection to the root is a bijection from S to the root support. Consequently the root law identifies the whole joint law

`q=φ_#μ_r`.

No conditional independence between branches is assumed. In the exact case, deterministic relations eliminate the branch-coupling freedom.

For binary sign relations `X_j=s_ij X_i`, this identifies at most two global response patterns. It discovers a one-bit operational descriptor even when U has arbitrarily many hidden states. Any extra hidden variation that leaves all these responses unchanged remains unidentified. Nothing here licenses an intervention `do(root bit)` or a unique microscopic causal graph.

### Proposition 2. Robust factor certificate

Allow edge violation probabilities

`e_ij=P[X_j≠g_ij(X_i)]`.

For any globally compatible μ, define `R(x)=φ(x_r)` and `q=R_#μ`. Then

`TV(μ,q)=μ({x:x≠R(x)})≤Σ_(ij∈T)e_ij`.

**Proof.** R fixes its image S, and preserves the root. For every y∈S, `q(y)≥μ(y)`, while q is zero outside S. Thus the total variation distance is exactly μ(S^c). If every edge relation holds, induction along the tree gives x=R(x), so S^c is contained in the union of the edge-violation events. Apply the union bound. ∎

For a target `f∈[0,1]`, the prediction error is at most this TV bound. For `f∈[−1,1]`, it is at most twice the bound. The certificate is simultaneous for all bounded targets because it controls the entire response law. Conditional predictions on an event of small probability require a separate denominator bound.

The sum is sharp: take a fair root and disjoint rare edge failures. For two symmetric pair contexts with error rates .02 and .03, compatible global laws can have TV distances anywhere from .03 to .05 from the coherent law. The nested-failure and disjoint-failure constructions attain the endpoints. Choosing a Markov completion would select only one member of this interval without empirical authorization.

For a candidate signed relation on a cycle with negative sign product, every response vector violates at least one edge. Thus `Σ_cycle e_e≥1` is necessary for any common joint law. Three pairwise perfect anticorrelations with fair singleton marginals violate this inequality. They are overlap-consistent local tables but admit no global response law. Disturbance, non-shared contexts, or genuine contextuality must then be addressed before reconstructing a classical hidden response world.

## 5. Sharp experimental cost for certifying a proposed one-bit factor

This is the most useful quantitative candidate. The detailed frozen statement is also in `world_theorem_frozen.md`.

### 5.1 Fixed inputs and target

Fix m≥2 and a sign pattern `s∈{−1,+1}^m`, learned from separate training or supplied in advance. Put `S={s,−s}`. Fix a nonempty family H of nonempty allowed contexts. Each trial returns the full raw X_C for one chosen context C on a fresh independent unit. Across trials choices may be adaptive.

For root r, define

`R_r(x)=(x_r/s_r)s`, and `q_r(μ)=(R_r)_#μ`.

This is the unique law supported on S with the same root marginal as μ, and

`TV(μ,q_r(μ))=μ(S^c)`.

For a general μ the q_r can differ for different roots; their distances to μ are nevertheless equal. The aim is to distinguish laws supported on S from laws with `μ(S^c)≥ε`, or issue a one-sided certificate that this mass is at most ε. It is not tolerant estimation.

A context C detects an incoherent response x exactly when `x_C∉{s_C,−s_C}`. Let B be the nontrivial subset on which x differs from s. This happens exactly when C meets both B and its complement.

### 5.2 The context cut-hitting LP

Define

`τ(H)= min Σ_(C∈H) w_C`

subject to

`w_C≥0`, and `Σ_(C crosses B) w_C≥1` for every nontrivial cut B.

If infeasible, set τ=∞. Complementary cuts are redundant. This LP weights **contexts so that they hit every cut**. It should not be confused with literature called fractional cut covers that instead weights cuts to cover edges. For ordinary edge contexts it is the classical unit-demand cut-cover relaxation from connectivity design.

When τ is finite, it is at least 1. Its max–min equivalent is

`1/τ = max_(λ∈Δ(H)) min_(nontrivial B) Σ_(C crosses B)λ_C`.

An optimal experimental distribution is `λ_C=w_C/τ`. This is a fully specified design problem, not an appeal to whichever experiment seems informative.

### Theorem 3. One-sided upper bound

Choose each context independently from λ, and reject immediately when its raw outcome is inconsistent with S. If `μ(S^c)≥ε`, each trial rejects with probability at least ε/τ. Therefore, for `0<ε<1` and `0<δ<1/2`,

`N=ceil[ log(δ) / log(1−ε/τ) ]`

trials suffice for false acceptance probability at most δ. In particular,

`N≤ceil[(τ/ε)log(1/δ)]`.

Every μ supported on S is accepted with probability 1. A close distribution outside S need not be accepted; this is intentionally not a tolerant tester.

A precise confidence formulation avoids a selection fallacy. Define `U_N=min{1,τ(1−δ^(1/N))}` after zero violations, and U_N=1 otherwise. Then for every μ,

`P_μ[ μ(S^c)>U_N ]≤δ`.

This is unconditional coverage, not a claim of 1−δ probability conditional on accepting.

**Proof.** For every bad x, its cut B has λ-crossing probability at least 1/τ. Averaging over x gives a violation probability at least μ(S^c)/τ. The independent zero-violation probability is at most `(1−μ(S^c)/τ)^N`. Rearrangement gives both assertions. ∎

### Theorem 4. Adaptive lower bound with full raw outcomes

Let a possibly sequential adaptive tester stop almost surely, have finite expected number of context queries under

`q_0=Uniform({s,−s})`,

and have an acceptance event A satisfying

- `P_(q_0)(A)≥1−δ` (completeness at this specified balanced null),
- `P_μ(A)≤δ` whenever `μ(S^c)≥ε` (soundness).

Then

`E_(q_0) N ≥ τ(H) kl(1−δ,δ) / [−log(1−ε)]`.

This is a worst-case/balanced-null lower bound, not a lower bound at every root-biased coherent distribution. Soundness alone cannot imply it, since a tester could refuse to certify everything.

**Proof.** For a nontrivial cut B, let x_B be s flipped on B, and let

`q_B=Uniform({x_B,−x_B})`,

`μ_B=(1−ε)q_0+ε q_B`.

The two support pairs are disjoint. Every root remains fair, so `q_r(μ_B)=q_0` and `TV(μ_B,q_0)=μ_B(S^c)=ε`.

If C does not cross B, `q_(B,C)=q_(0,C)` exactly. If C crosses B, the local support pairs are disjoint, and

`KL(q_(0,C) || μ_(B,C))=−log(1−ε)`.

Let N_C be the number of times context C is queried. The direct sequential likelihood-ratio identity and binary data processing at A give

`Σ_(C crosses B) E_(q_0)N_C ·[−log(1−ε)] ≥ kl(1−δ,δ)`.

Scaling the expected counts gives a feasible solution of the defining LP. Summing yields the bound. This direct argument uses absolute continuity only in the q_0-to-μ_B direction. A generic lemma stated with mutual absolute continuity must not be invoked without addressing that distinction. ∎

For a certificate asserting `μ(S^c)≤ε`, where false certification is prohibited only for strict alternatives `μ(S^c)>ε`, use η>ε in the construction and let η decrease to ε. The same lower bound follows by continuity.

For `0<ε≤1/2` and `0<δ≤1/4`, these bounds imply

`Θ( τ(H) ε^(−1) log(1/δ) )`

worst-case certification complexity. The upper bound is fixed-sample; the lower bound permits adaptive stopping and bounds its expectation under the balanced null. No exact-constant equality is claimed for arbitrary ε and δ.

### 5.3 Exact interface comparisons

- **Singleton contexts only:** τ=∞. A nontrivial cut is never crossed. The balanced coherent law and a cut-flipped balanced law have identical observed laws but TV distance 1.
- **Edges of a tree:** τ=m−1. Each fundamental cut forces its unique crossing edge to have weight at least 1; unit weights attain the bound.
- **All pairs:** τ=m/2. Each singleton cut must have incident weight at least 1, so summing gives `2Σw≥m`. Uniform weight `1/(m−1)` attains the bound.
- **All k-subsets, 2≤k≤m:** τ=m/k. Sum the singleton-cut inequalities for the lower bound. Uniform weights attain it because a singleton cut has the minimum number of crossing k-subsets. This formula is false at k=1, where no cut can be crossed.
- **One full context:** τ=1. Each trial checks the entire response pattern.

The gain from bigger contexts is in independent preparations. If k-response contexts each require k equally expensive protocol evaluations, `N·k` stays of order `m/ε` in the complete k-context family. There is no automatic reduction in total scalar measurements.

### 5.4 Discovery cost and an actual small-model output

The signs must not be optimized on the same zero-violation validation data without correcting for selection.

One simple learn-and-certify procedure is:

1. Use a separate training sample on the edges of an available spanning tree. A single outcome pair sets each candidate relative sign. Under an exactly coherent response law this learns all signs, up to the irrelevant global sign, in m−1 pair queries.
2. Fix those signs and choose the validation design from H. Regardless of whether training was correct, the holdout theorem gives a valid certificate for the chosen candidate.
3. Estimate one root marginal from independent samples. For a binary root, `n_r≥log(2/δ_r)/(2η²)` gives root TV error at most η with failure probability δ_r.
4. Output the two-atom law q_hat. On a successful structural certificate with tolerance ε_s, its error is at most `ε_s+η`, with total failure probability at most `δ_s+δ_r`.

Under all k-subset contexts, training can use overlapping contexts to connect up to k−1 new signs per unit; its cost is separately counted. Under arbitrary noise, the algorithm may decline to certify. It has not promised to identify every near-coherent model or find the globally best sign pattern/tree.

Concrete count: with m=20, a tree interface, structural tolerance .025 and confidence error .025, 2,804 validation trials suffice using the elementary exponential bound. Root tolerance .025 and error .025 require 3,506 root samples. Including 19 training pairs, 6,329 prepared units suffice for a .05-TV certificate with confidence .95 when the checks pass. The response space has 1,048,576 possible patterns. This is a favorable structural instance, not a general exponential improvement for learning arbitrary million-outcome distributions.

### 5.5 The observational boundary is data-dependent

The τ theorem is deliberately worst case. Singleton-only observations do not make every dataset ambiguous to every tolerance.

If all signed singleton marginals have a common probability α of +1, the sharp compatible range of mass outside `{(+1)^m,(−1)^m}` is

`[0, min{1,m·min(α,1−α)}]`.

For α≤1/2, the upper bound follows by charging each nonconstant vector at least one +1; use the symmetric argument when α≥1/2. If mα≤1, mass mα uniformly spread over one-+1 vectors attains the bound, with the remaining mass all −1. If `1≤mα≤m−1`, a symmetric mixture of fixed-Hamming-weight nonconstant vectors attains off-support mass 1. The coherent mixture attains 0.

Thus deterministic singleton marginals identify the entire joint law. Near the deterministic boundary they can certify an approximate factor even though τ=∞ for uniform worst-case certification. This is exactly why feasible support and the observed b must be retained, rather than reducing all learning questions to the access hypergraph alone.

## 6. Target-specific experimental and computational consequences

### 6.1 Which new contexts are necessary?

In the full-support Fourier setting, a target `f=Σ_A a_Aχ_A` is identified after adding contexts precisely when every support A with a_A≠0 is contained in at least one available context. Minimal-cost added context selection is therefore a weighted covering problem.

This does not require identifying the whole joint law. A sparse f may need only one missing interaction. Conversely, adding arbitrarily many samples to contexts that never contain a required interaction cannot help without extra model restrictions.

The optimization is NP-hard for a general context menu. Reduce weighted set cover by assigning one disjoint pair of response coordinates to each universe element, taking f to be the sum of those pair characters, and giving each available set a context containing the pairs of its elements. It covers exactly the required pair interactions associated with those elements. The target description remains sparse.

This hardness concerns selecting an unrestricted experiment menu. It does not make the tree certificate hard, nor imply that every physically meaningful menu is difficult.

### 6.2 Noise for an already identified target

If `f=c+Σ_C g_C(x_C)` is a known decomposition, estimate each term using n_C independent context samples. Hoeffding gives

`P(|f_hat−E f|≥t) ≤ 2 exp[−2t² / Σ_C osc(g_C)²/n_C]`.

For total sample budget N and ideal real-valued allocation, the best allocation for this bound is proportional to `osc(g_C)`, yielding denominator `(Σ_C osc(g_C))²/N`. Integer rounding adds at most one sample per nonconstant term. Optimizing over valid decompositions gives a target-dependent sufficient sampling cost. This is an upper bound, not a minimax theorem.

### 6.3 Computational status of τ

The general LP has one constraint per nontrivial cut, hence an exponential explicit description. For ordinary graph-edge contexts, violated constraints are found by minimum cut, so standard separation-based linear optimization is polynomial in the explicit graph size and input bit precision. This is existing network-design machinery.

For complete k-context families, the exact formula removes the optimization, and a uniform k-subset can be sampled without enumerating all contexts. For arbitrary implicit hypergraph menus, no blanket polynomial-time claim is made. Writing down the allowed experiments may already be exponential.

## 7. Nearest prior art and exact claim boundaries

The sources below are primary papers. The comparisons were checked on 2026-11-03. “Strong comparator” means a directly inspected relevant result, not an assertion that every latest paper has been exhaustively reviewed.

### 7.1 Marginals, counterfactuals, and contextuality

**Tian–Pearl, 2000, _Probabilities of Causation: Bounds and Identification_.** Sharp counterfactual bounds and the distinction between interventional marginals and individual causal attribution are classical. For two binary response marginals, probability of benefit has the familiar Fréchet interval. Our response-type polytope and its coupling ambiguity do not improve this theory. [Primary paper](https://ftp.cs.ucla.edu/pub/stat_ser/r271-A.pdf)

**Duarte et al., _An Automated Approach to Causal Inference in Discrete Settings_.** Their canonical discrete causal models reduce broad partial-identification questions to polynomial optimization, with anytime bounds. Our finite linear response-law model is a simpler special case; it does not solve general latent-SCM polynomial constraints. [Primary article](https://pmc.ncbi.nlm.nih.gov/articles/PMC11566246/)

**Abramsky–Brandenburger, 2011, _The Sheaf-Theoretic Structure of Non-Locality and Contextuality_.** A family of local measurement distributions, global extensions, and linear obstructions to extensions are already central objects. Our negative-cycle and parity demonstrations are standard examples of the same marginal/global-section phenomena. Our positive tree factor result concerns uniqueness/approximation within an already admitted classical global-response model, rather than a new definition of contextuality. [Primary paper](https://arxiv.org/abs/1102.0264)

**_Generalized Cut Polytopes for Binary Hierarchical Models_, 2020.** Binary marginal polytopes indexed by simplicial complexes and their relation to cut polytopes are established. Our Fourier support criterion is the elementary dual description of the marginalization map. It is not a claim that a hierarchical log-linear factorization of the unknown distribution has been learned: a marginal constraint and a log-density interaction constraint are different things. [Primary paper](https://arxiv.org/abs/2008.00043)

**Chen–Darwiche, 2024, _Identifying Causal Effects Under Functional Dependencies_.** Functional dependencies can restore identification and reduce required observability in causal graphs; their results explicitly handle the interaction with positivity assumptions. The present support-collapse argument is not the first use of determinism to identify causal quantities. Its particular target is a whole operational response law, with empirical approximate relations and a restricted-context sampling cost. [Primary paper](https://proceedings.neurips.cc/paper_files/paper/2024/file/9e4b14eb6f16fe7b5818a8d633a0606a-Paper-Conference.pdf)

### 7.2 The quantitative theorem's actual ancestors

**Kaufmann–Cappé–Garivier, 2016, Lemma 1; Garivier–Kaufmann, 2016, lower-bound proof.** Their expected-count/KL change-of-measure method and optimization over alternatives directly provide the design principle behind Theorem 4. Here every useful KL is the same number, and its support is a cut-incidence row, so the generic information lower bound reduces to a covering LP. The quoted KCG lemma assumes mutual absolute continuity; our singular-support alternatives require the direct one-direction likelihood-ratio argument supplied above. This is a technical specialization, not a new lower-bound method. [KCG primary paper](https://jmlr.org/papers/volume17/kaufman16a/kaufman16a.pdf), [GK primary paper](https://proceedings.mlr.press/v49/garivier16a.pdf)

**Nitinawarat–Atia–Veeravalli, 2013, _Controlled Sensing for Multihypothesis Testing_.** Sequential control of experiment choices and max–min KL design are classical, with asymptotic optimality results. Our hard alternatives are an explicit finite controlled-sensing family. The zero-violation upper bound additionally covers an arbitrary composite alternative by a pointwise detection inequality; it is not an application of a general theorem about learning arbitrary latent worlds. [Primary paper](https://arxiv.org/pdf/1205.0858)

**Jain, 2001, _A Factor 2 Approximation Algorithm for the Generalized Steiner Network Problem_.** The graph-edge τ LP is the unit-cut-demand instance of the standard connectivity cut relaxation. Its minimum-cut separation oracle and optimization formulation are not new. The statistical interpretation of the LP is the content of the present specialization. [Primary paper](https://www.cs.toronto.edu/tss/files/papers/Jain2001_Article_AFactor2ApproximationAlgorithm.pdf)

**Local testing of repetition codes.** S is a signed binary repetition code. Sampling a local equality check and rejecting on a violated constraint is a standard one-sided local tester. The distinction is between Hamming distance of one word and TV mass outside the code for a distribution of fresh words. The worst detectable non-codeword can differ in one coordinate, which produces the m-dependence. [Primary local-testing treatment](https://drops.dagstuhl.de/storage/00lipics/lipics-vol325-itcs2025/html/LIPIcs.ITCS.2025.65/LIPIcs.ITCS.2025.65.html)

**Goldreich–Ron, 2023, _Testing Distributions of Huge Objects_.** Distributions over long response strings with only local access are already an explicit testing model, including support-on-string-property questions. Their principal metric is Hamming earth mover, and their oracle permits multiple local probes into a sampled object. Our result instead fixes one joint context per fresh unit and uses TV. The present restricted-access LP theorem has not been located verbatim there, but the overarching task is not new. [Primary paper](https://theoretics.episciences.org/12765/pdf)

**Blanca–Chen–Štefankovič–Vigoda, 2023.** Coordinate-conditional testing gives strong high-dimensional identity-testing guarantees under approximate tensorization, using conditional and full-sample access. Their `O-tilde(n/ε)` rate is for KL; the TV lower bound is `Ω(n/ε²)`. These must not be compared numerically to our `m/ε` support test without matching metric, null support, and oracle. [Primary paper](https://proceedings.mlr.press/v195/blanca23a/blanca23a.pdf)

**Novelty verdict.** The row-space theorem is classical. The coupling and parity examples are classical. The tree TV certificate is an elementary retraction/union-bound consequence. The τ upper/lower comparison is a concrete synthesis of established local-testing, cut-relaxation, and controlled-sensing methods; no source inspected stated this exact restricted-context formulation, but that does not support a novelty claim. A paper-level contribution would require a substantially broader or stronger result, or a new application where the interface and distinction genuinely matter.

### 7.3 Strong causal-representation comparators

**Li–Kaba–Ravanbakhsh, AISTATS 2025, Theorems 3.1–3.2.** With paired pre/post-intervention data, faithful latent SCMs, smooth invertible mixing, and their continuous-noise assumptions, identifiable causal abstraction is governed by atoms generated by the non-descendant sets of available intervention targets. Theorem 3.2 can disentangle additional singleton targets under its further condition. Thus recovering an abstraction instead of microvariables is already a precise CRL result. Our setup drops invertible measurement and a supplied latent DAG, but only learns an operational response factor, a weaker claim. [Primary paper and theorem text](https://arxiv.org/html/2503.10834)

**Yao et al., ICLR 2025, Theorem 3.1.** Invariance and sufficiency constraints identify specified invariant blocks up to smooth reparameterization under their generative assumptions. The paper explicitly accommodates non-causal invariances. Consequently “representations emerge from invariants rather than supplied causal labels” is not by itself a novel position. Our discontinuous support relations and finite context oracle are different assumptions, not a dominance result. [Primary paper](https://proceedings.iclr.cc/paper_files/paper/2025/file/85381f4549b5ddf1d48e2e287d7d3d15-Paper-Conference.pdf)

**Varici et al., JMLR 2025.** Score-based CRL obtains latent graph/representation identification from one stochastic hard intervention per node for linear mixing, and two per node for general transformations under its assumptions; matching intervention pairs need not be known. Soft interventions have weaker guarantees. Our theorem does not recover those latent coordinates or mechanisms and therefore cannot be advertised as stronger identification from weaker assumptions. [Primary paper](https://jmlr.org/papers/v26/24-0194.html)

**Lee–Jin–Aragam, 2026 preprint, Theorems 2.1 and 4.5–4.7.** They give finite-sample recovery of a linear latent DAG, mixing matrix, and unknown multi-node targets with logarithmically many environments under a strongly separating intervention design, additional noise-scale intervention conditions, and finite-sample conditioning/signal assumptions. The hidden SEM and observation mixing are both linear, and the intervention/noise design is substantive. This is a direct warning against claiming that all contemporary CRL is merely population identifiability or requires one environment per variable. [Primary manuscript](https://arxiv.org/html/2603.25796v1)

### 7.4 Active system identification

**Mania–Jordan–Recht, JMLR 2022.** Active nonlinear system identification with guarantees uses transitions linear in a known state-action feature map, and plans/tracks trajectories to excite feature directions. It provides a parametric statistical rate. Our restricted-context result learns no transition law and assumes independent prepared units rather than one evolving trajectory. [Primary paper](https://jmlr.csail.mit.edu/beta/papers/v23/20-807.html)

**Wagenmaker–Simchowitz–Jamieson, ICML 2021.** Task-optimal exploration already asks which aspects of a linear system must be learned for a decision task, rather than demanding uniform model recovery. Therefore “learn only enough explanatory structure for the task” is an established methodological idea. The present example adds an explicit response-coupling obstruction and a very different observation interface, not a replacement theory. [Primary paper](https://proceedings.mlr.press/v139/wagenmaker21a/wagenmaker21a.pdf)

**Chatzikiriakos–Jamieson–Iannelli, AISTATS 2026.** Finite-hypothesis linear system identification has excitation-sensitive lower/upper bounds and an active design method. The available inputs and persistent-excitation properties are already part of the complexity statement. Our result makes the analogous dependence on joint-measurement contexts explicit for a simple structural certificate. [Primary paper](https://proceedings.mlr.press/v300/chatzikiriakos26a.html)

## 8. What the category-theoretic program can honestly take from this

The response-model fiber, its identifiable linear observables, and its support-conditioned quotients are different objects. Their distinction matters operationally.

A categorical account is useful if it preserves at least these interfaces:

1. **Restriction:** extending the experiment panel shrinks the compatible-model fiber; it does not automatically select a unique member.
2. **Partial composition:** products of identified observables need additional joint information or a support relation that makes the product reducible.
3. **Certificate:** an empirical functional relation can make a previously unjustified composite identifiable on feasible support.
4. **Approximation:** finite samples warrant a confidence region or a TV neighborhood, rather than an exact new equation.
5. **Resource accounting:** both the physical context cost and the statistical distinction probability enter the next-experiment problem.

The positive example discovers arrows `X_i=φ_i(X_r)` from observations; it does not assume them as the algebraic doctrine. Compositions along a learned tree are then justified on the certified response support. But the mathematics that makes this possible is already functional dependence and statistical testing. Merely repackaging the diagram as a category is not an additional discovery theorem.

A worthwhile next research target would be a general theory of **which small response factors can be certified under a constrained context menu**, with instance-dependent information bounds and explicit discovery cost. The balanced one-bit theorem is a clean calibration case, not evidence that the general problem has been solved. Moving to multiple factors immediately revives unknown coupling: two internally coherent components can each have a learned one-bit descriptor while their joint law remains unidentified.

### 8.1 Extension to affine response factors

The companion `world_code_extension.md` gives complete proofs for a supplied binary affine response set `A=c+V`. It generalizes the one-bit example without assuming that a physical world decomposes into independent components.

- **Support certification:** for each allowed context J, collect every dual vector in V⊥ supported inside J. Local experiments can certify support in A uniformly over arbitrary response distributions exactly when these vectors span V⊥. The quantitative design LP hits every nonzero coset of V. Its value τ gives the same upper bound and uniform-code-null adaptive lower bound as the repetition-code theorem, with order `τ ε^(−1)log(1/δ)` in the stated parameter range.
- **Internal-law identification:** assuming support in A, exact context marginals identify its probability law exactly when their accessible characters cover all of `F₂^m/V⊥`. The number of covered classes is the rank of the marginalization map. Generating those classes as a vector space is insufficient because the expectations of products remain unknown.
- **Neither condition implies the other:** two duplicated response bits can have certifiable equality relations but an unidentified coupling. Conversely, every proper projection of a three-bit parity code is unconstrained, so it cannot certify parity, although even its three singleton marginals identify the law conditional on even parity.

This clean separation is a useful extension of the methodological example. The underlying linear-code duality, Fourier algebra, and local-testing conversion are established mathematics. The companion gives direct attribution and exhaustive rational checks in dimensions at most three. It does not learn an unknown code or identify latent causal interventions.

## 9. Reproducible checks

Run:

`python world_checks.py`

The script writes `world_checks_results.json`. It checks:

- parity ambiguity and exact marginal ranks for m=2 through 7;
- a generic three-variable chain fiber versus its data-driven two-point collapse;
- infeasibility of the negative triangle;
- the exact [.03,.05] tree-TV interval by linear programming;
- 600 sampled finite laws for the retraction TV identity and union bound;
- the residual coupling of two coherent components;
- primal/dual cut-LP equality and τ=m/k for 28 complete-context instances, plus tree and singleton cases;
- 2,547 raw-context KL computations for the balanced cut alternatives;
- 54 biased-singleton cases matching the sharp ambiguity formula;
- the stated finite sample counts.

These finite checks supplement the proofs. They are not substitutes for the sampling contract, a novelty audit, or an empirical experiment on a physical device.

An independent adversarial check is recorded in `world_review.md`, with separate exact rational diagnostics in `world_review_checks.json`. It found no blocking defect in the frozen certification theorem and specifically checked the balanced-null, strict-threshold, unconditional-coverage, fresh-unit, and integer-rounding qualifications.

The affine extension is checked separately by `world_code_checks.py`, `world_code_exhaustive.py`, and `world_code_review_checks.py`. The final combined review and exact scope of the checks are recorded in `world_final_review.md`.
