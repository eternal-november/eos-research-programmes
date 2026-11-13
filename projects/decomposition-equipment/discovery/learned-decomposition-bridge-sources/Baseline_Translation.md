# Exact translation of mechanism sparsity learning into typed decomposition witnesses

28 October 2026

## Finding and scope

A successfully fitted mechanism sparsity model already supplies jointly learned latent factors, local positive transition kernels, learned influence interfaces, an observation mechanism, and a normalized temporally compatible joint law. Translating that construction into witnesses is sound bookkeeping, not a new positive realization theorem or an additional assembly obstacle. Independent conditional innovations do not imply independent component dynamics.

The strongest matched comparison is **not one theorem that uniformly dominates the others**. Use the CLeaR 2022 exponential family theorem on its stated class; use the separately versioned 2026 nonparametric extension when its different sufficient influence conditions hold. The latter explicitly characterizes residual entanglement and can combine action and temporal identification. Neither supplies finite communication, bounded autonomous memory, finite precision, controller information acquisition, or finite sample confidence certificates. These are genuine additional requirements when the target asks for them, not defects in the prior work.

This note is a comparison and semantic bridge input. It does **not** identify a continuous model as a proved instance of the proposed finite state contract. It makes no contract amendment, package acceptance, novelty claim, or claim that an optimization run reached the theorem premises.

## Sources and exact revision reconciliation

**S22.** Lachapelle et al., *Disentanglement via Mechanism Sparsity Regularization: A New Principle for Nonlinear ICA*, CLeaR 2022, [published PDF](https://proceedings.mlr.press/v177/lachapelle22a/lachapelle22a.pdf), especially §§2.1–2.6, Theorems 4–5, Definitions 1–2, Assumptions 1–2, and Appendix A.3.4. Main theorem uses fixed observation noise variance; Appendix A.4.1 separately addresses learning it when the latent dimension is strictly smaller than the observation dimension. Appendix A.4.2–3 contains additional exponential family/initialization extensions; these are not silently folded into the main theorem below.

**S26.** Same authors, *Nonparametric Partial Disentanglement via Mechanism Sparsity: Sparse Actions, Interventions and Sparse Temporal Dependencies*, **arXiv:2401.04890v2, 31 July 2026**, [version pinned HTML](https://arxiv.org/html/2401.04890v2), [same version PDF](https://arxiv.org/pdf/2401.04890v2). The HTML and PDF use different counters. The user specified HTML theorem numbers:

| Subject | HTML number and anchor | Same version PDF number |
|---|---|---|
| Continuous action identification | [Theorem 22](https://arxiv.org/html/2401.04890v2#Thmtheorem22) | Theorem 1 |
| Discrete action identification | [Theorem 24](https://arxiv.org/html/2401.04890v2#Thmtheorem24) | Theorem 2 |
| Temporal identification | [Theorem 32](https://arxiv.org/html/2401.04890v2#Thmtheorem32) | Theorem 3 |
| Action consistency | Definition 21 | Definition 13 |
| Temporal consistency | Definition 31 | Definition 14 |
| Combined consistency | Definition 36 | Definition 15 |
| Combining the two relations | Proposition 37 | Proposition 6 |
| Graphical criterion yields complete disentanglement | Proposition 38 | Proposition 7 |
| Non Markovianity or auxiliaries for the temporal assumption | Remark 50 | Remark 7 |

Assumptions 1–8 have the same numbers in these two renderings. Some HTML headings misleadingly display “Definition 0” or “Proposition 0”; internal links and PDF resolve the intended labels. This is a rendering issue, not evidence of a different theorem.

**Local target evidence.** `related_work_audit_20261028/Discovery_Target_Comparators.md`; proposed contract v0.3, `contract_revision_20261028/final_artifacts/Proposed Research Completion Contract.txt`, corresponding to supplied Library `` content version 1. No contract file is changed. O1–O8 are conjunctive packages; passing a constituent below is not package completion.

## Shared model vocabulary and what is not supplied

Write (m=d_z), (d=d_a), and fix the source observation horizon (T). The observations are vectors (X^1,\ldots,X^T); the recorded auxiliary vectors are (A^0,\ldots,A^{T-1}). Auxiliary coordinates can be continuous actions, discrete actions, intervention labels, or environment indices. They are **not** supplied latent values or supplied target allocations.

Both sources learn a decoder or mixing function, transition mechanisms, and graphs:

\[
\theta=(f,p,G^z,G^a),\qquad
p(z^t\mid z^{<t},a^{<t})=\prod_{i=1}^m
p_i(z_i^t\mid z_{\operatorname{Pa}^z_i}^{<t},a_{\operatorname{Pa}^a_i}^{<t}).
\]

For S22, (p_i) is specified by its exponential family natural parameter function (\lambda_i). An edge (G^z_{ij}=1) permits dependence on **the past history of coordinate (j)**, not just its last value. (G^a_{i\ell}=1) permits dependence on the history of auxiliary coordinate (\ell). Some permitted lags need not be active. The graph is not a supplied physical wiring diagram; it is learned support of functional/probabilistic influence.

The emission kernel is

\[
E_\theta(dx\mid z)=\mathcal N(f(z),\sigma^2 I)(dx),
\]

with a Dirac kernel when (\sigma=0). The model family fixes the latent dimension and the relevant structural assumptions; it does not supply (f,p,G). A fixed model universe is legitimate discovery input. The learned coordinate count is nevertheless **not** an unknown output of these particular theorems.

The sources compare conditional observation laws for every auxiliary sequence in the declared support, at the fixed horizon (T). A structural causal interpretation requires a justified protocol/causal model. In S22 the authors explicitly say causal interpretation is not required by the identification theory (§2.1, footnote 3). S26 does not model the distribution of the auxiliaries (§2.1). Consequently, do not convert arbitrary observational action labels into a guarantee under new policies. The normalized product below gives a causal *kernel construction* for fixed/exogenously set actions; identifying that construction with an actual intervention law is a separate access assumption. In particular, an ordinary conditional distribution given an entire adaptively generated action sequence is not automatically its interventional counterpart.

## Exact S22 theorem ledger

### Base class and Theorem 4 premises

1. Hidden coordinates are continuous; (m\le d_x). (f:\mathcal Z\to f(\mathcal Z)) is a diffeomorphism onto its image. (X^t=f(Z^t)+N^t), with common isotropic Gaussian variance, noises mutually independent across time and independent of latent and auxiliary variables.
2. Conditional independence and masked history dependence are as above. With fixed sufficient statistic (s_i) (called (T_i) in S22), base measure (h_i), natural parameter (\lambda_i), and log normalizer (\psi_i),
   \[
   p_i(z_i^t\mid h)=h_i(z_i^t)\exp\{s_i(z_i^t)^\top\lambda_i(h)-\psi_i(h)\}.
   \]
   The models are genuine members of this normalized family, not arbitrary signed factorizations.
3. Each sufficient statistic is minimal. Equivalently, no nonzero linear combination of its components is almost everywhere constant on its support.
4. The stacked natural parameter has sufficient variability: there are (km+1) admissible history/action points, potentially from different times, whose (km) differences from a reference natural parameter are linearly independent.
5. Two models in the same declared family agree on (P_{X^{\le T}\mid a^{<T}}) for every admissible auxiliary sequence.

Theorem 4 gives affine equivalence of sufficient statistics and the dual natural parameter transformation. Specifically, for some invertible (L) and vectors (b,c), on the common noiseless image,

\[
s(f^{-1}(x))=L s(\hat f^{-1}(x))+b,
\quad
\hat\lambda(\hat f^{-1}(x^{<t}),a^{<t})
=L^\top\lambda(f^{-1}(x^{<t}),a^{<t})+c.
\]

This is an equivalence between model representations, not a procedure for applying (f^{-1}) to noisy measurements.

### Additional Theorem 5 premises and staged conclusions

Let \(\mathbb R_G^{r\times s}\) denote matrices supported on a binary pattern (G), and \(\mathbb R_C^m\) vectors supported on a node subset (C).

**S22.5.1** (k=1), and the componentwise stacked statistic (s:\mathcal Z\to s(\mathcal Z)) is a diffeomorphism.

**S22.5.2** There are (|G^z|_0) admissible history/action/lag points ((h_r,a_r,\tau_r)) such that

\[
\operatorname{span}_r
\{D_{z^{\tau_r}}\lambda(h_r,a_r)
[Ds(z_r^{\tau_r})]^{-1}\}
=\mathbb R_{G^z}^{m\times m}.
\]

These conditions already imply **some common latent permutation (P)** with
\(PG^zP^\top\subseteq\hat G^z\).

**S22.5.3** For each auxiliary coordinate \(\ell\), there are \(|\operatorname{Ch}^a_\ell|\) admissible points/perturbations/lag choices such that

\[
\operatorname{span}_r
\{\lambda(h_r,a_r+\epsilon_r E_{\ell,\tau_r})-
\lambda(h_r,a_r)\}
=\mathbb R_{\operatorname{Ch}^a_\ell}^{m}.
\]

Perturbed actions must remain in support. This gives \(PG^a\subseteq\hat G^a\) for the same permutation.

**S22.5.4** Total sparsity satisfies
\(\|\hat G^z\|_0+\|\hat G^a\|_0\le\|G^z\|_0+\|G^a\|_0\).
Then both inclusions are equalities. This is a premise on a perfectly fitted solution, satisfied by a suitable global minimum edge solution, not a theorem that an arbitrary regularization coefficient finds one.

**S22.5.5** For every latent index (r), there exist sets (I,J\subseteq[m]), (L_a\subseteq[d]) with

\[
\left(\bigcap_{i\in I}\operatorname{Pa}^z_i\right)
\cap\left(\bigcap_{j\in J}\operatorname{Ch}^z_j\right)
\cap\left(\bigcap_{\ell\in L_a}\operatorname{Ch}^a_\ell\right)=\{r\}.
\]

Only with this extra criterion does Theorem 5 conclude permutation equivalence in S22 Definition 2: the matrix in sufficient statistic space is permutation scaling. Thus individual coordinates are recovered up to the induced coordinatewise invertible transformations, not identified in their original physical units. With (s_i(z)=z), this is coordinate permutation, nonzero scaling and shift. Without S22.5.5, graph equality does **not** by itself assert complete coordinate disentanglement.

**What it says about learning.** §§2.6 and 4 give a VAE based estimation method and experiments. Exact law matching, the requisite sparsity, and global optimization are not finite data consequences of Theorem 5. Approximate ELBO optimization alone is not a witness of its hypotheses. [S22, §§2.1–2.6 and Appendix A.3.4](https://proceedings.mlr.press/v177/lachapelle22a/lachapelle22a.pdf).

## Exact S26 theorem ledger

### Assumptions 1 through 4

**A1.** (Z^t\in\mathbb R^m\), (m\le d_x); (f:\mathbb R^m\to\mathbb R^{d_x}) is a (C^1) diffeomorphism onto its **closed** image. The independent Gaussian emission model above holds, permitting zero noise variance.

**A2.** Conditional factors have Lebesgue densities on \(\mathbb R\) with support all of \(\mathbb R\), and factorize given all past latent and auxiliary variables. At (t=1), this specifically means
\[
p(z^1\mid a^0)=\prod_i p_i(z_i^1\mid a^0).
\]
No arbitrary correlated hidden initial law is included by that assertion. Common random (A^0), if subsequently marginalized, can induce marginal initial correlation; so can a noninitial observation window after interacting dynamics. Neither licenses replacing the theorem's initialization by any desired correlated law.

**A3.** Mechanism (i) depends only on the latent and auxiliary parent histories selected by row (i) of (G).

**A4.** Local densities are (C^2) jointly in current latent value, latent history and auxiliary history for continuous auxiliaries; the auxiliary domain is regular closed. For discrete auxiliaries, (C^2) is required in the latent arguments for each fixed auxiliary history. The derivative assumptions below use log densities on their stated domain. “Full support” should not be silently replaced by a quantitative density lower bound.

The known parameters are (m,\sigma^2); the unknown parameters are (f,p,G). Neither finite memory nor stationarity is required; auxiliaries can include time. [S26 §2.1](https://arxiv.org/html/2401.04890v2#S2.SS1).

### Common exact observation premise and diffeomorphism transport

Observational equivalence is equality of observation distributions for all auxiliary sequences at the fixed (T). Under the source assumptions, equivalence entails a common noiseless image and the entanglement diffeomorphism (v=f^{-1}\circ\hat f), taking learned coordinates to true coordinates, with

\[
\hat p(z^t\mid z^{<t},a^{<t})
=p(v(z^t)\mid v(z^{<t}),a^{<t})|\det Dv(z^t)|.
\tag{D}
\]

This transports whole transition kernels and initialization; it does not identify a same time hidden state from a noisy observation. [S26 Definitions 6–7 and Proposition 8](https://arxiv.org/html/2401.04890v2#S2.SS4).

### Theorem 22 for continuous auxiliaries

Set (q=\log p\). For almost every current (z\in\mathbb R^m), and each auxiliary coordinate \(\ell\), Assumption 6 requires \(|\operatorname{Ch}^a_\ell|\) choices of time (t_r), earlier auxiliary lag \(\tau_r\), latent history (h_r\), and auxiliary history (a_r) such that

\[
\operatorname{span}_r\{[H_{z,a}^{t_r,\tau_r}q(z\mid h_r,a_r)]_{\cdot,\ell}\}
=\mathbb R_{\operatorname{Ch}^a_\ell}^{m}.
\]

Together with A1–A4 for both models and exact observational equivalence, this implies \(PG^a\subseteq\hat G^a\) for some permutation (P). Adding \(\|\hat G^a\|_0\le\|G^a\|_0\) gives **action consistency**:

\[
\hat G^a=PG^a,\qquad v=c\circ P^\top,
\]

where (c) is a (G^a)-preserving diffeomorphism, and (D) holds. It does **not** claim (G^z) identification. [Theorem 22](https://arxiv.org/html/2401.04890v2#Thmtheorem22), [Assumption 6](https://arxiv.org/html/2401.04890v2#Thmassumption6).

### Theorem 24 for discrete auxiliaries

Replace the Hessian column condition by Assumption 7: for almost every current (z) and every \(\ell\), admissible one-coordinate auxiliary changes span the affected coordinates,

\[
\operatorname{span}_r\{
D_z^{t_r}q(z\mid h_r,a_r+\epsilon_rE_{\ell,\tau_r})-
D_z^{t_r}q(z\mid h_r,a_r)\}
=\mathbb R_{\operatorname{Ch}^a_\ell}^{m}.
\]

All perturbed actions must be admissible. With the same exact equivalence and action sparsity bound, the conclusion is the **same action consistency**, not a temporal graph theorem. This is the relevant unknown intervention target result; the intervention interpretation must be established by the experimental protocol, not inferred just from a label. [Theorem 24](https://arxiv.org/html/2401.04890v2#Thmtheorem24), [Assumption 7](https://arxiv.org/html/2401.04890v2#Thmassumption7).

### Theorem 32 for temporal dependencies

Assumption 8 is materially different from the preceding conditions. For almost every current (z), one must find \(\|G^z\|_0\) admissible time, lag and history choices with **\(z=h_r^{\tau_r}\)** and

\[
\operatorname{span}_r\{H_{z,z}^{t_r,\tau_r}q(z\mid h_r,a_r)\}
=\mathbb R_{G^z}^{m\times m}.
\]

With A1–A4 and exact equivalence, this gives \(PG^zP^\top\subseteq\hat G^z\). Adding \(\|\hat G^z\|_0\le\|G^z\|_0\) yields **temporal consistency**:

\[
\hat G^z=PG^zP^\top,\qquad v=c\circ P^\top,
\]

where (c) preserves both (G^z) and \((G^z)^\top\), and (D) holds. This theorem alone does **not** identify (G^a). The matrix span notation above spells out the matrix dimensions implicit in the source. [Theorem 32](https://arxiv.org/html/2401.04890v2#Thmtheorem32), [Assumption 8](https://arxiv.org/html/2401.04890v2#Thmassumption8).

**Why there is no blanket dominance over S22.** In a time homogeneous first order Markov model with no auxiliaries, setting the selected past value equal to current (z) removes the varying history argument. The displayed Hessians span at most one dimension. If \(\|G^z\|_0>1\), A8 fails. The source explicitly discusses this and uses non Markovian examples; its exponential family specialization relaxes the condition. Consequently a continuous first order sparse Gaussian system can be covered by S22 without being covered by this nonparametric temporal theorem. [S26 §3.9.3, Remark 50](https://arxiv.org/html/2401.04890v2#S3.SS9.SSS3).

### Exact residual ambiguity and combining identification

A (G)-preserving map (c), with dependency matrix (C), satisfies

\[
G_{i,\cdot}\not\subseteq G_{j,\cdot}\ \Longrightarrow\ C_{ij}=0.
\]

Equivalently, \(C^\top\mathbb R_G\subseteq\mathbb R_G\). Such diffeomorphisms form a group. They can mix several coordinates. Consistency is therefore a substantive characterization of remaining representation ambiguity, already in prior work. It is not mere latent label permutation.

When both action and temporal theorem premises hold, the two consistency conclusions can be aligned to a common permutation; the remaining (c) preserves all of (G^a,G^z,(G^z)^\top). This uses the combination result, not an unjustified assumption that the initial permutations coincide. With S26 Assumption 5,

\[
\left(\bigcap_{j\in\operatorname{Ch}^z_i}\operatorname{Pa}^z_j\right)
\cap\left(\bigcap_{j\in\operatorname{Pa}^z_i}\operatorname{Ch}^z_j\right)
\cap\left(\bigcap_{\ell\in\operatorname{Pa}^a_i}\operatorname{Ch}^a_\ell\right)=\{i\},
\]

this reduces to permutation and componentwise invertible maps (complete disentanglement). Neither result chooses a unique physical ontology or original units. [S26 §§3.3, 3.6–3.7](https://arxiv.org/html/2401.04890v2#S3.SS6).

**Source notation caveat.** HTML Definition 36 / PDF Definition 15 prints \(\tilde G^a=P^\top G^a\), \(\tilde G^z=P^\top G^zP\), but also \(v=c\circ P^\top\). This disagrees with Definitions 21/31 and the conclusion proved in Appendix A.4.1. Here the consistent convention is \(\hat G^a=PG^a\), \(\hat G^z=PG^zP^\top\), \(v=c\circ P^\top\). The accompanying formal note gives a direct common alignment argument; the printed inconsistency is not silently attributed as a theorem improvement.

The described equivalences relate **models that remain in the stated model class**. Do not claim that every arbitrary graph preserving diffeomorphism applied to every model preserves conditional independence. Nor does an equivalence relation by itself provide a computable enumeration of every observationally equivalent finite resource architecture.

## What the learned model already provides

| Object | Already supplied by a valid fitted model | Identification strength or limitation |
|---|---|---|
| Latent coordinates | (m) hidden continuous coordinate processes and learned observation map | S22 graph plus affine statistic gauge; full coordinate identification needs its graphical criterion. S26 allows explicitly restricted entanglement until its criterion holds. Count (m) is supplied. |
| Local transition mechanisms | Nonnegative normalized (p_i(\cdot\mid\text{parent histories})) | Transported under the allowed representation change; function weights need not themselves be uniquely identifiable. |
| Temporal graph | A learned (G^z) | Identified by S22 staged premises or S26 Th32, not by S26 Th22/24 alone. |
| Action to latent allocation | A learned (G^a) | Identified by S22 staged premises or S26 Th22/24, not by Th32 alone. This is real interface assignment discovery. |
| Positive joint history law | Iterated product of kernels and emission, integrated over latent variables | Already normalized and time coherent within the horizon; no new assembly search is necessary. |
| Initialization | (t=1) member of the same conditional factorization, explicitly product given (a^0) in S26 | Not arbitrary hidden correlated initialization. Correlation can develop persistently under coupled transitions. |
| Decoder and measurement noise | Learned forward (f), known theorem noise level; Gaussian emission kernel | A noisy measurement does not supply exact latent state. No local sensing placement is identified. |
| Alternatives | Representation quotient/consistency restrictions at population level | Not finite sample credible coverage, quantitative stability, or a complete catalogue of bounded physical implementations. |
| Estimation | VAE and sparse graph estimation procedures plus experiments | Population identifiability conditional on exact matching is not finite sample/global optimization certification. |

## Witness schema translation

The following is a semantic interpretation into a **measurable stochastic witness schema**, not an unproved embedding into the old finite graph and span equipment.

| Typed decomposition object | Translation from the learned model |
|---|---|
| Component occurrence | Mechanism occurrence ((i,t)), retaining both indices even when mechanism parameters are shared. |
| Local state type | Own coordinate history (S_i^{t-1}=\mathbb R^{t-1}), or the source support analogue; update appends (z_i^t). If the learner supplies a finite sufficient state, that can replace the history, but the theorem does not promise one. |
| Input ports | One typed latent history port from each (j\in\operatorname{Pa}^z_i), and action history ports \(\ell\in\operatorname{Pa}^a_i\). |
| Output ports | Current latent value and, for the history presentation, retained history needed by later consumers. Fanout shares the **same producer value**, not independent resamples. |
| Local stochastic event | (p_i(dz_i^t\mid h_{\operatorname{Pa}^z_i},a_{\operatorname{Pa}^a_i})), with deterministic append update. Its event witness retains the incoming values and the sampled outgoing value. |
| Boundary compatibility | Incoming port projections equal the corresponding producer history projections, including shared/repeated uses. |
| Initialization witness | The learned conditional (t=1) kernel; no revealing reset is assumed. |
| Readout component | A possibly global emission node (E(dx^t\mid z^t)). Its cost and placement are not free in a physical refinement. |
| Whole state and event witnesses | Actual latent trajectories, action boundary values, and readout events with the probability measure below; retain time and component occurrences rather than quotienting identical labels. |
| Assembly witness | The generative product measure together with the commuting port and state projections. Positivity and normalization are checked at the kernel level. |
| Representation transport | Pushforward along (v) and permutation; local occurrencewise transport is immediate for componentwise gauges, but a mixing (c) need not preserve a chosen distributed resource layout. |

For each fixed auxiliary history,

\[
\mathsf W_\theta^a(dz^{1:T},dx^{1:T})=
\prod_{t=1}^{T}\left[
\left(\bigotimes_{i=1}^{m}K_{i,t}(dz_i^t\mid
z_{\operatorname{Pa}^z_i}^{<t},a_{\operatorname{Pa}^a_i}^{<t})\right)
E_\theta(dx^t\mid z^t)\right].
\tag{W}
\]

Products are iterated kernel products, not a claim that histories or components are unconditionally independent. Normalization follows by integrating the last emission and then all last coordinate kernels, repeatedly backward. Marginalizing a suffix recovers the prefix law. Thus overlap restrictions from this **one retained joint witness** are automatically compatible. A law on only the original (T) steps does not identify unobserved longer horizon behavior.

The state/event projections carry hidden values only **inside the generative witness**. They are not an oracle delivered to the learner or controller. The observation channel can remain noisy, and local states need not be observed to be legitimate hidden components. Likewise a structural edge is not a proof that a digital robot already receives that value. A subsequent implementation theorem must say which internal channels it builds and what information its controller actually senses.

For a measurable scalar kernel, an independent uniform random seed plus a conditional quantile map implements a mathematical sample; emissions can use independent Gaussian seeds. This shows the usual independent innovation realization is available. Cross time parent dependence still produces interacting and correlated components. Exact real valued sampling is not a finite random bit or finite precision guarantee.

The full semantic statement and proof are in `Baseline_Semantic_Realization.md`.

For a concrete Gaussian neural mechanism implementation with positive variances and valid masks, normalization and parent dependence can be certified syntactically from trusted normalized primitives. A checker need not redo fitting or solve a separate compatibility search. The harder unprovided checks concern claimed exact data agreement, identifiability premises, constrained physical resources, and finite data confidence—not a fabricated difficulty in normalizing that circuit.

## O1 through O8 ledger

Legend: **PASS constituent** means the indicated narrowly matched mathematical claim holds. **NOT DISCHARGED** means the full v0.3 package has not been met. **NOT CLAIMED** identifies work outside the source theorem, not a falsified assertion. **SCOPE MISMATCH** identifies an actual different class.

| Package | What truly passes in the matched continuous population setting | Exact reason the whole package is not discharged |
|---|---|---|
| O1 Readout based specification | PASS constituent: unknown coordinates, decoder, dynamics and target allocation are inferred from mixed readouts within a declared class; exact law versus fitting are distinguishable. No actual positive frame is supplied to the discovery problem. | SCOPE MISMATCH: fixed known coordinate count, continuous full support, diffeomorphic noiseless map, and source initialization rather than the selected finite state unknown count class. Finite sample protocol, resource bounds and causal coverage need a separate specification. |
| O2 Positive decomposition and assembly | PASS constituent: positive local kernels, learned influence interfaces, compatible initialization, normalized correlated temporal law, exact behavioral agreement under the fitting premise, and stated representation ambiguity. Construction by generative parametrization counts. | NOT CLAIMED: growing family finite bandwidth/memory/locality certificates excluding hidden global implementations, architecture coverage within that implementation class, and its obstruction branch. Do not invent failure of positivity or temporal compatibility. |
| O3 Witness checking and complexity | PASS constituent: a supplied valid kernel model has a short mathematical normalization argument; a normalized Gaussian circuit admits a syntactic normalization/mask check. | NOT CLAIMED: independent executable checker with exact/certified encodings of arbitrary smooth functions, theorem hypothesis checks, finite precision, witness size and search/checking bounds. A formula for a density is not automatically a decidable normalization/equality certificate. |
| O4 Finite data and unresolved information | PASS constituent: population identifiability and explicit residual equivalence; full influence/coverage assumptions are exposed. | NOT CLAIMED: selection valid uncertainty sets, finite sample rates, support recovery margins, lower bounds or policy transfer under sampled coverage. Exact rank/spanning assumptions have no quantitative condition number bound. |
| O5 Environment types and physical implementation | PASS constituent: meaningful local conditional dependency signatures and action influence allocation. Hidden state remains valid. | NOT CLAIMED: reusable controller capability language, preservation/matching theorem, runtime sensing access, finite messages, decoder placement, memory/randomness/precision ledger. A conditional independence graph is not already that capability certificate. |
| O6 Structural theory and discovery bridge | PASS constituent: there is a direct positive stochastic semantic interpretation. | NOT CLAIMED: sound/complete comparison to retained presentation/refinement/equipment machinery or a demonstrated extra discovery/checking/reuse capability. Rephrasing (W) as a categorical composite is not the required contribution. |
| O7 Crossing cuts and coherent recovery | PASS constituent: projections of the same joint law agree on overlaps, including nonlaminar subsets. | NOT CLAIMED: arbitrary separately proposed crossing mechanisms glue, witness sensitive boundary descent, all degree typed 2 Segal recognition, refinement/interchange, or optimal simultaneous repair. Ordinary marginal consistency must not be presented as those stronger claims. |
| O8 Integrated validation | PASS constituent: a strong prior comparator and exact theorem ledger are available. | NOT DISCHARGED: no integrated finite resource discovery theorem, structural gain/ablation, independent full acceptance, or novelty result follows from this translation. |

## Exact additional bridge obligations

1. **Implementation relative to a learned witness.** Prove that the selected learned kernels factor through finite local states and bounded interfaces, or provide certified approximations. Charge channel memories, sensor/readout placement, all persistent common state, program representation, arithmetic and precision. Fixed parameter description length is not itself mutable runtime memory; keep those costs separate.
2. **Uncertainty and scope.** Link sampled readouts to a covered set of possible kernels/architectures, including adaptive selection and quantitative excitation or separation where needed. Neither qualitative identifiability nor low training loss supplies this.
3. **Witness sensitive resource transport.** State which coordinate changes preserve a physical realization/capability type. Observationally equivalent representatives can have different measured costs relative to a separately fixed, untransported message/state primitive language. Transporting all physical, readout, task and cost metadata preserves the represented operational feasibility: gauge ambiguity alone is not a physical obstruction. Preserve ambiguity instead of treating an inexpensive representative as the unique physical system.
4. **Actual structural contribution.** Show a gain from retained boundary/witness/refinement information—an additional sound implementation, a demonstrably sharper certificate, reusable verification with a proved cost advantage, or an exact obstruction/repair result. The existing normalized assembly cannot be claimed again as that gain.
5. **Class alignment.** A finite state theorem about independently learned positive transducers may be useful, but requires its own readout learning premise or finite approximation theorem. Continuous identifiability does not establish a finite alphabet or finite state model by relabeling it.

The baseline therefore closes the alleged general gap “joint learning produces parts but no positive whole.” The remaining research target is the precisely delimited resource, information, uncertainty and witness transport guarantee—not positive generative assembly in general.
