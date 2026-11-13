# Positive and predictive realization: theorem-level related-work audit
**Date:** 28 October 2026. **Status:** bounded audit complete; classification review passed. Not a priority determination.

## Conclusions first

1. **Finite Hankel identification is established realization theory.** The delivered finite-horizon TV lemma is an explicit conditioning-dependent, adaptive-policy bound between *two valid controlled laws*. Its telescoping mechanism has a particularly close antecedent in Chen–Bai–Mei, Proposition D.1; the exact displayed constants were not found verbatim. It should not be advertised either as a new spectral-learning principle or as an already-checked verbatim corollary of Hsu–Kakade–Zhang.
2. **Calibrated reset frames and channel-cone certificates are genuine scoped sufficient results, not raw-data architecture discovery.** Cartesian structure uses a classical equivalence-relation criterion. Simplicial positive coordinates and fixed-frame local-polytope LPs are established mechanisms. A normalized positive retraction makes the restricted-span LP complete for arbitrary local generators, but only within the declared frame/protocol.
3. **Permutation and noisy-feedback families supply concrete identification and resource-accounting results.** Their ingredients are familiar—coset interfaces, distinguishability, binary ICA, finite-field rank—but their exact causal, observational, and resource restrictions matter. They are not examples of unrestricted latent-architecture identification.
4. **The defect bound is exactly a probability-flattening rank bound, not a new invariant.** Separately, the reflection example strengthens the benchmark packaging, not the basic positive-realization obstruction. Benvenuti–Farina (2003), §3 Example 4, already exhibit, in a **scalar positive-linear system**, a *whole infinite Hankel* of nonnegative rank 3 requiring more than 3 positive states. The reflection construction additionally supplies simultaneous two-channel, no-reset, bounded-marginal and arbitrary-period properties; those additions should not be erased by citing only a probability clock.
5. **Compact-witness results are format-sensitive.** Simulation identities, tensor contraction, graph-state cut ranks, TT ranks, structural-algebra invariant downsets, and moment sparsification are established tools. The delivered restrictions and their combination give useful certificate theorems and explicit counterexamples. They do not give a general proposer, identify the true physical decomposition, or show every equivalence proof must be large.

| Delivered cluster | Best-supported relationship | Remaining technical residue / scope |
|---|---|---|
| Finite predictive certificate and TV | Standard realization theorem; explicit specialized error proof using established telescoping mechanism | Exact deterministic rank/conditioning constants and valid-law formulation; priority unresolved |
| Calibrated Cartesian resets | Direct structural specialization plus a constructive application | Population calibration to operational positive coordinates, combined port construction |
| Channel cones, profiles, retracts | Standard simplicial-cone/local-polytope mechanisms; useful fixed-frame extension | Profile-minimal deterministic messages; checkable normalized retract as completeness certificate |
| Permutations and feedback ICA | Explicit instances / combinations of established ingredients | Exact resource costs, observational ambiguity, quantitative proposed-frame verification |
| Defect and reflection | Defect exactly ordinary flattening; persistent gap has exact classical antecedent | Simultaneous strengthened benchmark properties, not a new general obstruction principle |
| Compact witnesses | Standard core mechanisms plus restricted certificate theorem and separating examples | CP/TT-vs-circuit proof separation; rich-control completeness and nonvacuous rank-`2n` family |

**Excluded from the result inventory:** the unreviewed internal positive-simulation-span follow-up. The published positive-semiring properness theorem is relevant background, not a delivered theorem of this project. The locality/resource-preserving analogue remains open.

## Evidence, notation, and limits

The audit inspected the delivered proof notes, independent reviews and relevant primary literature. It did not independently formalize the proofs, exhaustively search all prior work, or reproduce every numerical regression. A checked proof or a genuinely useful instance is not automatically a priority claim. “Direct specialization” below is used only where the hypotheses and conclusion have an explicit translation.

**Source identity.** Earlier delivered archive: Library ``, version **1**, `Data driven decomposition proof checkpoint.zip`; SHA-256 `b27255e669f9adde1b3293699af7c0369ad397868ff2b1457b0f29ed1f537b3c`. Latest archive: ``, version **0**, `Interacting_Architecture_Research_Sources_20261028.zip`; SHA-256 `e04e26549414dd9a89c684e9850bd252c172e0d86e42193748b87401d9bdf581`.

Both delivered archives were inspected without substitution.
Below, **P/** means the earlier archive's `proofs/` directory; **S/** means `Interacting_Architecture_Research_Sources_20261028/sources/`. These are exact archive-member locators, not claims that the original shared working directories are present. Earlier proof status can be cross-checked against `SOURCE_MANIFEST.tsv`.

---

## 1. Finite predictive realization and the finite-data TV bridge

### Delivered statements and hypotheses

**Loci:** P/`Finite_Observable_Behavior_Certificate.md`, §§2–4, especially lines 15–69.

Let two valid input-total controlled laws have global Hankel rank at most `r`. Choose the same `r` basis prefixes and suffixes. An invertible probability block `B`, its symbol-shifted blocks, and its prefix/suffix boundary vectors produce the usual signed predictive realization. Equality of those finitely many entries determines the entire law **within that rank-bounded universe**. The same causal controller therefore produces the same closed-loop transcript law. A small observed block does not itself certify a global rank upper bound.

If both basis blocks have smallest singular value at least `σ`, their finite tables differ entrywise by at most `ε`, and at most `m` outcomes accompany each command, put `κ=1/σ`. For every common adaptive controller and horizon `H` the note proves
\[
\operatorname{TV}(f^{\pi}_{0:H},g^{\pi}_{0:H})
\le \min\{1,[2r\kappa+r^2\kappa^2+Hm(r^2\kappa^2+r^3\kappa^3)]\epsilon\}.
\]
This is a deterministic comparison of **valid laws**, not automatically the guarantee of an unconstrained spectral estimator.

### Primary antecedents and exact translation

The predictive dimension/minimal linear realization principle is classical. Singh–James–Rudary, *Predictive State Representations: A New Theory for Modeling Dynamical Systems*, Theorems 4–6, identifies finite system-dynamics rank with linear predictive dimension, including controlled systems. Prefix/suffix coordinates and shifted Hankel blocks are the same construction up to row/column convention. This covers the exact finite-basis mechanism, not a positive physical realization. [Primary paper](https://faculty.cc.gatech.edu/~isbell/reading/papers/uai2004psr.pdf).

A closer comparison for the error proof than a generic spectral-learning reference is Chen–Bai–Mei, *Partially Observable RL with B-Stability*, **Proposition D.1**, Appendix D.1. It expresses policy-conditioned TV error through an initial-state term and a sum of operator-error terms weighted by unnormalized predictive prefixes. Transposing conventions and treating the terminal evaluation as an additional endpoint gives the same telescoping architecture. [Primary paper, Appendix D](https://arxiv.org/pdf/2209.14990).

The delivered specialization obtains the needed bounds directly from the chosen probability basis:
- inverse perturbation gives operator error at most `(rκ+r²κ²)ε`;
- a true-law prefix row has norm at most `√r κ f(h)`;
- an arbitrary event/continuation-policy column has norm at most `√r`, because its entries are **unnormalized** continuation probabilities;
- averaging prefix masses under the causal controller sums to one; the at-most-`m` outcomes give the displayed linear-`H` term.

Thus the proof does not raise an operator norm to the `H`th power and does not divide by rare basis-prefix probabilities. An externally specified controller memory can be held fixed when evaluating a basis-prefix continuation, so adaptivity is genuinely covered. This verifies the mathematical bridge to the established telescoping mechanism; it is not a claim that the exact B-stability norm parameters or constants are identical.

Hsu–Kakade–Zhang, *A Spectral Algorithm for Learning Hidden Markov Models*, **Theorem 6 and Lemma 12**, has a different estimator/model setup and intermediate multiplicative error accumulation. It is an important baseline, but its theorem is not literally the above valid-controlled-law, arbitrary-policy statement. [Primary final paper](https://www.cs.columbia.edu/~djhsu/papers/hmm-jcss-final.pdf).

### Classification and what remains

**Known exact-realization mechanism; explicit specialized perturbation proof, exact-constant priority unresolved.** The useful residue is an auditable operational bound tied to a finite probability certificate, not a new PSR principle. Statistical use still requires coverage, action propensities/exogeneity where relevant, simultaneous confidence bands, defensible rank membership and conditioning, and control of adaptive model selection. It yields neither infinite-horizon safety nor exact support identification. A signed predictor is not yet a positive typed architecture.

---

## 2. Calibrated resets and Cartesian operational frames

### Delivered statements

**Locus:** P/`Calibrated_Reset_Frame_and_Coupled_Ports.md`, §§1–3 and 6–8.

A rank-at-most-`N` process with `N` preparation histories and an exhaustive readout probe having exact Kronecker-delta pairing has dual predictive bases. Probe probabilities become nonnegative operational coordinates and give an `N`-state positive realization. This is a strong population calibration assumption; it does not identify physical microstates.

For stochastic reset operators `P_i`, assume idempotence, pairwise commutation and positive diagonals. Let `F_i=∏_{j≠i}P_j` and `Q=∏_iP_i`. Require the **whole-family** support condition
\[
R(P_i)\cap R(F_i)=\Delta.
\]
Within each `Q`-class, the component equivalence classes form a Cartesian coordinate frame. Fiber sizes may depend on the public/boundary class. Pairwise checks alone do not establish this condition.

### Baseline mapping

The stochastic part reduces each idempotent with positive diagonal to recurrent blocks with identical positive stochastic rows; commutation supplies a common faithful invariant measure and conditional-averaging interpretation. This is classical stochastic-idempotent structure, not a new classification. Historical attribution should not be compressed to “Flor first”: older Doob results are relevant; the report does not make a priority assertion for that lemma.

The strongest precise structural match is Chen–Ponomarenko, *Tensor products of coherent configurations*, **Theorem 3.1, Corollary 3.2, Definition 3.3 and Lemma 3.4**: commuting equivalence relations, complementary joins/meets and atomic Cartesian decompositions. Translate relation composition/join into support of products of positive reset matrices; restrict to each `Q`-class for the connected/full-product universe. The delivered whole-family intersection condition is the complement condition, not ordinary pairwise independence. [Primary paper](https://arxiv.org/pdf/2105.10679).

### Classification and limits

**Direct structural specialization plus a concrete operational construction.** The proof usefully exposes assumptions sufficient to derive a positive frame from recorded calibration, then asks whether dynamics admit appropriately charged ports. It does not make arbitrary crossing frames jointly refinable or show that uncalibrated noisy logs identify these coordinates. Exact zeros, idempotence and delta calibration are fragile population properties; a robust finite-data replacement is additional work.

---

## 3. Observable channel cones, minimal deterministic messages, and positive retractions

### A. What the profile and simplicial-cone theorem actually says

**Locus:** P/`Observable_Channel_Cones_and_Minimal_Deterministic_Ports.md`, §§1–6.

Fix the physical frame, public state, full product private-input domain, one-round deterministic outgoing encoders, and a shared/boundary instruction chosen from the **public transcript only**. The profile of local input `x_i` records the entire outside marginal `(b,y_{-i})` as a function of `x_{-i}`. Any admissible encoder must distinguish unequal profiles. Equal-profile classes therefore give the coarsest necessary deterministic information partition **for this protocol**, not for arbitrary stochastic, interactive or side-channel protocols.

The resulting message cells are non-signalling. For a normalized cell kernel `H(y|x)`, let `U_i` be its mode-`i` unfolding span and `C_i=U_i∩R_+^{X_i×Y_i}`. Non-signalling gives every element a common row-sum functional. When every `C_i` is simplicial, its normalized extreme rays are local channels and positive coordinate inverses produce a nonnegative core `G` with total mass one:
\[
H=(A_1\otimes\cdots\otimes A_k)G.
\]
The important hypothesis is **positivity of the coordinate inverse on the cone**, not merely existence of an unconstrained Tucker decomposition.

### B. Nonsimplicial extension and its exact completeness boundary

**Locus:** P/`Positive_Channel_Retraction_Extension.md`, §§2–5.

Let `W_i` be all constant-row-sum local tables, `D_i=W_i∩R_+`, and `U_i\subseteq W_i` the observed span. Enumerating the normalized extreme rays of `C_i=U_i∩D_i` gives an LP. It is always necessary and sufficient for a shared-randomness realization whose local generators lie in `U_i`.

To remove this generator restriction, the note requires a **normalized positive retraction**
\[
P_i:W_i\to U_i,\quad P_i|_{U_i}=I,\quad P_i(D_i)\subseteq C_i,\quad \ell_iP_i=\ell_i.
\]
Existence is an LP: it suffices to check positivity on deterministic channel vertices. Applying `⊗P_i` to an arbitrary local-product realization fixes `H` and moves its factors into the restricted cones. Therefore the restricted LP is complete for arbitrary finite local shared-randomness generators **under this retraction hypothesis**.

A failed retraction search proves no impossibility. Failure of the restricted LP alone excludes only restricted generators. With a certified retract, its Farkas dual can be pulled back to exclude all generators in the fixed protocol, with a norm-controlled finite-error margin. Tensoring maps on distinct modes is not gluing overlapping physical decompositions.

### Primary comparisons

The simplicial-cone unmixing mechanism is a standard minimal/maximal tensor-cone fact. Aubrun–Lami–Palazuelos–Plávala, *Entangleability of cones*, **Theorem A (easy direction) and Corollary 4**, makes simplicial factors the setting where the positive tensor notions collapse. In the note, the restricted orthant cones and their positive coordinates supply an explicit finite-dimensional proof. This is not a new principle of nonnegative factorization. [Primary paper](https://arxiv.org/pdf/1911.09663).

At `U_i=W_i`, take `P_i=I`. The normalized local factors are stochastic channels, deterministic response functions are their vertices, and `G` is a probability distribution over tuples of such responses. The theorem is then exactly **finite local-polytope membership**. Brunner et al., *Bell nonlocality*, **§II, Eqs. (17)–(19)**, gives this deterministic-vertex decomposition, LP test and dual inequalities. The physical vocabulary changes, but the convex feasibility problem does not. [Primary review of the construction](https://arxiv.org/pdf/1303.2849).

Cohen–Comon–Gillis, *Some Theory on Non-negative Tucker Decomposition*, **Proposition 1**, is adjacent but not an exact replacement: it includes unique nonnegative CP decomposition/full-column-rank hypotheses not assumed here. A generic NTD citation therefore should not be used to erase the actual positive-coordinate argument. [Primary paper](https://orbi.umons.ac.be/bitstream/20.500.12907/41919/1/LVAICACohen.pdf). The theorem text was accessible through indexed primary-paper content; direct PDF retrieval was restricted.

Positive retracts are established ordered-vector-space machinery: Aubrun–Müller-Hermes, *Annihilating Entanglement Between Cones*, §2 immediately before Lemma 2.7, defines positive maps R,S with SR=I; here R is inclusion and S=P_i, with the additional channel-normalization constraint. Their Lemma 2.7 is a different retract-preservation theorem, not this LP-completeness statement. [Primary definition and lemma](https://link.springer.com/article/10.1007/s00220-022-04621-5). The audit did not locate a verbatim published theorem with exactly this normalization, observed-span LP and port application. That is an **unclosed exact-combination comparison**, not evidence of priority.

### Classification and obligations

**Known mechanisms; useful fixed-frame sufficient/completeness certificates and explicit deterministic-message application.** Proper retracts can provide genuine certified dimension reduction; the full-space case is the usual local polytope. Enumerating extreme rays or deterministic channels can be exponential. Reusing a certified kernel gives the same trajectories only after supplying a separately admissible, charged joint initialization. Neither non-signalling nor low predictive rank alone implies a local positive realization.

---

## 4. Explicit discovery and resource-accounting families

### A. Permutation interfaces

**Locus:** P/`Permutation_Interface_Discovery_Family.md`, §§2–9.

The universe is permutations of `n` labels with recorded uniform within-unknown-block shuffle resets, faithful label readout, and a lower transfer-probability guarantee. A transfer graph recovers the unknown partition with a coupon-collector-style finite-sample bound. This is not learning from an arbitrary unknown observation channel.

For block sizes `b_i`, the reset interface records label sets in each block and has
\[
Q=n!/\prod_i b_i!
\]
values. Reset rows coincide within each interface class and have disjoint supports across classes. Consequently ordinary rank and nonnegative rank both equal `Q`; every positive factorization needs at least `Q` interface states, and a minimal normalized stochastic interface is canonical up to relabelling. Crossing cuts reduce to membership-pattern cells: the number of witnesses is `∏_c |c|!`, and the joint interface count is `n!/∏_c|c|!`.

Under all permutation commands, the declared architecture with neither local messages nor a free boundary sensor needs `n!` boundary states, witnessed by a query/undo schedule and a diagonal Hankel block. Declared one-round messages repair it with explicitly charged alphabets. This is state-alphabet growth, not an exponential-in-`n` bit-storage claim: `log(n!)=Θ(n log n)`.

**Relationship:** an explicit concrete instance combining group-orbit/coset structure, disjoint-support nonnegative rank, distinguishability and elementary sampling. The note's full operational package was not found verbatim elsewhere; no priority claim is warranted. The value is the transparent cost ledger and crossing-witness multiplicity, not a new rank principle.

### B. Noisy finite-field feedback

**Locus:** S/`Noisy_Feedback_Architecture_Discovery.md`, Theorems 1–2; uniform-noise, proposed-frame, sensor-access and iid-pair-hardness extensions.

For binary `X'=AX+ξ`, `Y=BX`, invertible `A,B`, independent innovations with `0<p_j<1/2`, and uniform stationary hidden state, conditional Fourier signs identify `M=BAB^{-1}`. The residual `Y'−MY=Bξ` is a finite-field ICA model; log-Fourier coefficients identify the hidden axes and biases up to permutation. Positive bias fixes the usual binary sign/origin issue.

Yeredor, *Independent Component Analysis Over Galois Fields of Prime Order*, **Theorem 1**, identifies independent nondegenerate nonuniform sources under invertible prime-field mixing up to permutation/scaling; over the binary field scaling is trivial. This exactly covers the residual ICA mechanism. The temporal sign-identification step, declared observations and resource translation must still be checked rather than silently included in an “ICA” label. [Primary paper](https://arxiv.org/pdf/1007.2071).

For a known recovered frame and target block `S`, a deterministic incoming message is sufficient exactly when `A_{S,S^c}x_{S^c}` is constant on message fibers; the minimum alphabet is `2^{rank A_{S,S^c}}`. Separate senders require the corresponding sender-wise conditions. The ring family gives genuinely coupled crossing alternatives with sharply different interface costs. These are finite-field linear-image counts, not general nonlinear port minimality.

The proposed-frame checker uses positive residual-character means and vanishing pairwise covariances. For independent binary biased innovations, two parity features have zero covariance exactly when their source supports are disjoint; `n` nonempty disjoint supports must be singletons. Yeredor’s **Theorem 2** already proves that pairwise-independent nontrivial linear mixtures of independent nonuniform binary (or ternary) sources are a permutation/scaling of the sources. For binary outputs covariance zero is equivalent to pairwise independence. [Primary theorem](https://arxiv.org/pdf/1007.2071). The delivered margin, uniform character concentration and mixing argument turn this mechanism into a polynomial-sample **checker**, not an efficient frame proposer. Uniform innovations produce additional observable ambiguity, treated explicitly rather than hidden in a uniqueness claim.

**Relationship:** an established ICA identification mechanism extended into a concrete dynamic benchmark and quantitative certificate/resource accounting. Exact priority of the combined finite-sample checker was not established. The conditional LPN reduction concerns **iid stationary-pair records**, not a proof of hardness for unrestricted chronological trajectories. Actual sensor rowspaces, initialization and exogenous action sampling remain charged assumptions.

---

## 5. Hidden-mode defect and persistent positive-realization gap

These are different results and must not be conflated.

### A. The defect is a flattening rank

**Locus:** S/`Hidden_Mode_Defect_Review.md`, §§1–5, especially §4; related S/`Defect_Bound_Prior_Art.md`.

Assume two conditionally independent emissions from the **same hidden state** (both before, or both after, transition), `K` hidden states, minimal observable dimension `r`, and invertible observable unconditional transition `P`. With `E_{ab}=P^{-1}T_{ab}`, let `F` be the block matrix of `E_{ab}−E_aE_b`. The note proves
\[
r+\operatorname{rank}F
=\operatorname{rank}[E_{ab}]
=\operatorname{rank}[T_{ab}]
=\operatorname{rank}(\text{middle-letter probability flattening})
\le K.
\]
The first equality is an elementary block/Schur-complement rank identity; the last is factorization through the `K` hidden states. Therefore this is **exactly an ordinary observable probability-flattening rank lower bound**, not a distinct new invariant or a sufficient positive-realization criterion. The raw flattening bound does not require forming `P^{-1}`.

A stronger scoped exclusion also matters: if the **hidden** transition is invertible, diagonal emission operators preserve the correct reachable/observable subquotient and the defect vanishes. Nonzero defect excludes every invertible same-state independent-emission realization in this convention. It is not a generic marker of physical interaction. Mixed-time or arbitrary edge-emission models violate the needed factorization. Nonnegative-rank obstructions can exceed this ordinary-rank bound, as the note's paired-output example illustrates.

**Relationship:** direct rewriting of a standard factorization/rank obstruction, with useful explicit timing and quotient corrections. The technical residue is reliable applicability, not a new lower-bound mechanism.

### B. Whole-Hankel nonnegative rank 3 versus many persistent states

**Delivered proof loci:** S/`Persistent_Assembly_Obstruction.md`, §§“Positivity and the stronger static factorization bound,” “The persistent state lower bound,” “Matching rational upper bound and local realizations,” and “No observed reset”; S/`Persistent_Gap_Independent_Review.md`, §§3–7 and 10. S/`Positive_Dilation_Target.md` is contextual target/qualification material, not an additional proved-result inventory entry.

The explicit stationary two-binary-channel process uses a three-dimensional Lorentz-cone representation, two reflection symbols and a positive remainder. A fixed triangle separates the reachable and effect cones, giving **one nonnegative factorization of the entire infinite Hankel matrix** of size 3; ordinary and nonnegative Hankel ranks are exactly 3. Each marginal has a 3-state edge-emitting realization (6 states after state-emission conversion).

For rational angle `2π/q`, `q≥3`, the joint process has minimum edge-emitting positive size exactly `q`. An alternating-word sequence contains a peripheral `q`th root of unity; after correct accessible/coaccessible trimming, Perron periodicity forces at least `q` states. An invariant regular `q`-gon gives the matching upper bound. For irrational angle there is no finite positive realization. The conditional-product state-emitting version is bounded **between `q` and `4q`**, not proved to have exact minimum `q`. All observable symbol maps are invertible at the stated nonzero angles, hence there is no observable reset. The independent review addresses invisible hidden modes, stationarity and small polygons.

#### Exact prior antecedents, not just an analogy

Heller's invariant-polyhedral-cone characterization is restated precisely in Boyle–Petersen, *Hidden Markov processes in the context of symbolic dynamics*, **Theorem 4.38**. A reduced stochastic module is Markov-realizable precisely when a suitable finitely generated invariant cone exists. The article records the historical correction to Heller's original proof. This is the core distinction between a positive factorization and a cone preserved by **every symbol**. [Primary theorem exposition](https://arxiv.org/pdf/0907.1858).

Jaeger's OOM paper **Proposition 6 and §7** gives the finite-HMM invariant-cone criterion and probability-clock examples with period-dependent state lower bounds. Use the **2012 correction** for a valid clock parameter choice, and the pointed-cone/minimality qualification rather than indiscriminately applying an uncorrected proposition to nonminimal representations. [Original primary paper](https://www.ai.rug.nl/minds/uploads/oom_neco00.pdf), [2012 probability-clock correction](https://www.ai.rug.nl/minds/uploads/addendumProbClock.pdf).

Most importantly, Benvenuti–Farina, *Minimal Positive Realizations: A Survey of Recent Results and Open Problems*, **Kybernetika 39(2), 2003, §3 Example 4, pp. 223–224**, explicitly gives the periodic sequence `10,8,6,8,…`, an inner nonnegative factorization of its **infinite Hankel** with dimension 3, and proves that a positive realization cannot have dimension 3 because of peripheral eigenvalues `1,i,−i`. Thus “whole Hankel nonnegative rank can be smaller than persistent positive state size” already has an exact published antecedent. It must not be positioned as new merely by distinguishing whole-Hankel from bounded-block factorization. [Primary article and explicit matrices](https://www.kybernetika.cz/content/2003/2/217/paper.pdf).

This is a SISO positive-linear example, not itself a normalized stationary multi-symbol law: it establishes the gap mechanism, not the entire stochastic benchmark. The comparison uses its explicit example, **not** its broader iff criterion: the related 1998 nonnegative-factorization paper has a 2006 correction whose complete text was not inspected. That limits any reliance on its general theorem, but does not justify ignoring the explicit 2003 example. The authors' later survey also cites the gap together with the correction. [2022 survey](https://www.sciencedirect.com/science/article/pii/S0005109822002758).

#### Classification and residue

**Classical obstruction, strengthened explicit benchmark.** The simultaneous package—stationary two-channel process, bounded positive marginal realizations, full infinite Hankel nonnegative rank 3, no reset, and exact arbitrary-`q` joint edge-state requirement—is not shown by simply quoting the clock or the source's clock-plus-XOR masking observation. The triangle factorization, no-reset check and emission-convention conversions are additional verified arguments. No exact published counterpart for the whole package was established here; that is not a priority claim.

The result is a stress test for inference from local/linear/one-cut evidence. It is not a positive architecture-discovery theorem. The delivered obstruction gives an **exact finite disagreement**: a K-state candidate matching the first K+3 alternating-pair values would, by Cayley–Hamilton, match all of them, so for q>K some word of length at most 2(K+2) disagrees. Separately, the target note observes that finite-word equivalence plus compactness of the fixed-K stationary HMM parameter set gives a positive separation margin for each fixed budget. That additional existence-of-margin argument gives no effective numerical rate and no finite-data irrationality test.

---

## 6. Compact witnesses: what is easy to check, what can be large, and when completeness holds

**Main locus:** S/`Compact_Discovery_Certificate_Route.md`, §§1–6; independent checks in S/`Compact_Certificate_Independent_Review.md` and `Compact_Certificate_Checker_and_Nonvacuity_Review.md`.

### A. Certificate identities and honest verification cost

For a proposed positive hidden instrument `H_{uy}`, a signed map `F`, and a nonnegative normalized initializer `ν`, the identities
\[
\ell F=\mathbf1^T,\qquad FH_{uy}=T_{uy}F,\qquad F\nu=\alpha
\]
imply agreement on all words and adaptive controllers. These are the matrix simulation equations of Ésik–Maletti, *Simulation vs. Equivalence*, **Definition 3.1 and the immediately following equivalence proof**, transposed into column convention over the real field. The all-word implication is therefore a direct specialization. [Primary paper, §3](https://arxiv.org/pdf/1004.2426). Positivity is required of the hidden model and initializer, **not of the coordinate quotient `F`**.

With CP/TT encodings and a supplied exact contraction schedule, squared residual norms can be checked without enumerating the hidden product state space. The charged cost is the actual **doubled-network** contraction, explicit table/certificate sizes, intermediate tensors and rational bit lengths. Small static wiring width alone is insufficient. This is a verification theorem, not an algorithm guaranteed to propose a small certificate.

Markov–Shi, *Simulating Quantum Computation by Contracting Tensor Networks*, **Proposition 4.2**, identifies contraction complexity with line-graph treewidth and converts a supplied tree decomposition to a contraction order. Its contraction operation applies to finite real tensors too; the direct resource translation uses the actual residual network and variable index dimensions, not a quantum-state assumption. [Primary paper](https://arxiv.org/pdf/quant-ph/0511069). Further prior-art loci are documented in S/`Compact_Certificate_Prior_Art.md`.

### B. Two distinct completeness obstructions

1. **Initialized rank need not equal all-state predictive rank.** The shift-register example has a rank-one initialized iid law but no compatible normalized all-state quotient in the specified direction. A small reverse embedding does not fix that mismatch.
2. **Even a polynomial-rank all-state quotient may be exponentially large in CP/TT format.** A reversible local clocked circuit computes a Boolean quadratic parity feature with large rank across every balanced data cut. At a suitable phase, a slice of the quotient exposes that feature. Every ordering of data indices therefore has an exponential TT bond, and CP rank is also exponential. The graph has a narrow static description and the process has polynomial predictive rank. A short circuit decoder/cancellation proof nevertheless verifies the same behavioral identities.

The graph-state ingredient is established: Hein–Eisert–Briegel, **Proposition 3, Eq. (43)**, identifies binary cut rank with logarithmic Schmidt rank for the sign tensor of a graph. Passing from the sign tensor to the Boolean feature changes rank by at most one. [Primary paper](https://arxiv.org/pdf/quant-ph/0307130). The TT ingredient is likewise standard: Oseledets, **Eq. (2.1), Theorem 2.1**, relates unfolding ranks to TT bond sizes. [Primary paper](https://users.math.msu.edu/users/iwenmark/Teaching/CMSE890/TENSOR_oseledets2011.pdf).

**Relationship:** explicit separation between witness languages built from established rank and reversible-circuit ingredients. It does not prove that every proof system, every alternative architecture or every circuit-equivalence check is hard. The easy circuit verification uses the supplied structured inverse/cancellation computation; arbitrary circuit equivalence is not declared easy.

### C. Restricted rich-control completeness

**Locus:** §6, lines 226–325; rank-`2n` family at lines 327–389.

Assume invertible stochastic idle drift `D`; one-site action totals `DK_{i,k}`; and a polynomially described local control family whose **real linear span** with the identity is the entire equal-column-sum algebra
\[
\mathcal S_i=\{A:\mathbf1_i^TA=\lambda\mathbf1_i^T\}.
\]
The initialized process must match a minimal rank-`r` target. Actual controls can be positive and invertible, but point resets lie in their **signed span**—a strong calibration resource, not absence of calibration.

Finite-dimensional invariance under invertible `D` permits cancellation of drift. Signed point resets then make the initialized reachable space full. Thus initialized rank equals full predictive rowspace dimension. The local constant/contrast triangular algebra forces that rowspace to be a direct sum of **whole contrast tensor blocks indexed by a downward-closed family**.

This algebraic classification is a direct specialization of Akkurt–Barker–Wild, *Structural matrix algebras and their lattices of invariant subspaces*, **Theorems 1–4, especially Theorem 2**. Each local algebra contains block projections, arbitrary contrast endomorphisms and contrast-to-constant maps; their tensor product has the subset-incidence zero pattern. Invariant coordinate sets therefore form downsets. The source does not claim a new module classification. [Primary article DOI](https://doi.org/10.1016/j.laa.2004.05.009); theorem text inspected in the [author-paper text mirror](https://www.researchgate.net/publication/222141061_Structural_matrix_algebras_and_their_lattices_of_invariant_subspaces).

A product-function basis of size `r` yields a signed quotient of CP rank **exactly `r`**: upper bound by the basis, lower bound by its predictor-versus-hidden-state matrix rank. All TT ranks are at most `r`. Carathéodory applied in the normalized `(r−1)`-dimensional affine space gives an observationally equivalent nonnegative initializer on at most `r` configurations. Piazzon–Sommariva–Vianello, *Caratheodory–Tchakaloff Subsampling*, **Theorem 1.1**, states precisely this positive moment-preservation bound for a finite-dimensional function space; take that space to be the predictive rows including constants. [Primary theorem](https://drna.padovauniversitypress.it/system/files/papers/PiazzonSommarivaVianello_2017_CTS.pdf). This does not recover or preserve the original physical correlations or stationarity.

The explicit positive, invertible, coupled rank-`2n` family shows the assumptions are nonvacuous and no bit is simply discarded. Its shared selector and broadcast resources are explicitly charged; it also has a cheap squared-residual contraction. It does not prove minimal positive hidden state number or uniqueness of the physical frame.

**Relationship:** a restricted certificate-completeness theorem combining established algebraic and convex mechanisms, plus a concrete nonvacuity construction. The exact combination may be useful research residue; its priority was not resolved. A complete unknown-architecture proposer, sensor access, feasible initialization and a small actual contraction schedule still do not follow merely from small predictive rank. In generic rich-control models the top contrast block is present and `r` can equal the entire product state count.

---

## Published positive-simulation background—not a project result

Sokolova–Woracek, *Proper Semirings and Proper Convex Functors*, **Theorem 3.3 and Proposition 3.7**, proves properness for the nonnegative-real semiring: equivalent finite weighted systems are connected through finite positive simulations. Their proof uses a finitely generated intersection cone in a joint reachable space. This is the appropriate baseline for the excluded internal note. [Primary paper](https://arxiv.org/pdf/1802.07830).

Neither ordinary properness nor that cone construction preserves a prescribed tensor frame, component locality, message alphabets, hardware wiring or resource budget. Those constraints are exactly why citing the global result does not close the interacting-architecture target.

## Recommended positioning

> We have established finite behavioral certificates, several calibrated or fixed-frame positive-realization criteria, explicit resource-accounted coupled examples, and sharp limitations of rank and particular witness formats. Their core mechanisms have substantial classical antecedents. Some exact combinations and benchmark refinements remain worth comparing further, but the current record does not establish priority, general raw-data architecture discovery, or a locality-preserving positive-assembly theorem.

### Open comparison / verification register

- Exact historical priority of the finite-TV constants and the complete rich-control certificate combination remains unresolved.
- A verbatim channel-normalized positive-retraction theorem for this observed-span LP was not located; the positive-map mechanism is established.
- The complete simultaneous reflection benchmark was not matched to a single prior theorem; its basic whole-Hankel gap **was** matched.
- The 2006 correction to the older general nonnegative-factorization realization criterion was not fully accessed; no inference here depends on that uninspected general criterion.
- Independent numerical checks and supplied reviews support examples but do not replace proofs; this pass did not claim a fresh full regression run or formal verification.

