# Residual equivalence, conditional fibres, and the exact remaining realization gap

**28 October 2026 — candidate bridge actively tested, not a claim of full discovery completion.**

## Main findings

There is a constructive coordinate-level bridge from a learned consistency preorder to an invariant diagram of conditional component fibres and overlapping interfaces. Its overlap comparison preserves actual records, not merely marginals. It does not by itself make the fibres executable resource-bounded components.

A sharper result prevents over-interpreting that diagram: **an actual product-law equivalence can use a base-dependent fibre map only through a common symmetry of the entire conditional kernel family.** In particular, smooth scalar fibres over a connected Euclidean base cannot have genuine base-dependent residual mixing. The permitted sparsity envelope can therefore substantially overstate actual observational ambiguity. This is a product-transport rigidity argument; its scalar mechanism is standard one-dimensional/Knothe–Rosenblatt uniqueness, not a new transport theorem.

These conclusions use the learned positive kernels, not an assumed physical coordinate frame. They supply explicit tests and a natural witness scaffold. They do not yet synthesize unknown physical ports or prove the requested growing resource-constrained discovery theorem.

## 1. Exact input and the necessary-only boundary

Assume an actual successful population learner has returned latent coordinates, normalized conditional mechanisms, an emission, and a graph, with a proved residual guarantee after permutation alignment. In the continuous Lachapelle setting the relevant coordinate transformations are smooth diffeomorphisms on `R^d`.

For each graph whose preservation is guaranteed, write `N_i` for row `i`. Define a relation

\[
 i\preceq j\quad\Longleftrightarrow\quad
 N_i\subseteq N_j\ \text{for every required graph}. \tag{1.1}
\]

For action consistency the required graph is `G^a`; for temporal consistency it is `G^z` and `(G^z)^T`; use their intersection only when the combined conclusion holds with one common permutation alignment. The source's graph-preserving condition permits `c_i` to depend on `z_j` only when `i≼j`. This is a reflexive transitive preorder. Its equivalence classes are the strongly connected classes `i~j` iff `i≼j≼i`; after quotienting, strict dependence is acyclic.

Let `Γ_C` be the group of all `C`-preserving diffeomorphisms. The source establishes group closure; it also follows from the inverse-closed algebra of matrices with preorder sparsity. The **actual** residual transformations between two admissible observationally equivalent models are a subset of this group and must also transport their latent conditional laws. No assertion is made that every member of `Γ_C` is an actual observational equivalence.

An **upper set** `I` means `i∈I, i≼j ⇒ j∈I`. This convention matches the direction “coordinate i may depend on coordinate j.” Reversing the order would call these lower sets; no substantive claim depends on that naming convention.

## 2. Invariant interface diagram and exact crossing maps

For every upper set `I`, define `X_I=R^I` and the coordinate projection `π_I:R^d→X_I`. If `I⊆J`, let `π_{J,I}:X_J→X_I` be projection.

### Theorem 2.1 — maximal coordinate projections for the envelope

1. For every `c∈Γ_C` and upper set `I`, there is a unique diffeomorphism `c_I:X_I→X_I` with `π_I c=c_I π_I`.
2. These maps commute with all projections: `π_{J,I}c_J=c_Iπ_{J,I}`.
3. Conversely, if a coordinate subset `I` is not upper, its projection is not preserved by every member of `Γ_C`.

**Proof.** The components `c_i`, `i∈I`, use only coordinates in `I`, so they define `c_I`. The same holds for `c^{-1}`; projecting the two inverse identities shows that its induced map is the inverse of `c_I`. Uniqueness follows from surjectivity of `π_I`, and the projection identity follows coordinatewise. For the converse choose `i∈I,j∉I` with `i≼j`. The elementary shear `c_i(z)=z_i+z_j`, all other coordinates unchanged, is a `C`-preserving diffeomorphism with `C`-preserving inverse. Two points agreeing on `I` but differing in `z_j` acquire different projected images. QED.

The converse concerns the **envelope group** only. If that shear fails to preserve the required conditional product laws, it is not evidence of actual observational ambiguity. Section 4 makes this distinction effective.

### Theorem 2.2 — crossing and refinement retain exact coordinate records

For upper sets `I,J`, union and intersection are upper, and

\[
 \Phi_{I,J}:X_{I\cup J}\longrightarrow
 X_I\times_{X_{I\cap J}}X_J,
 \qquad z\longmapsto(z_I,z_J) \tag{2.1}
\]

is a canonical bijection/diffeomorphism. It is natural under every `c∈Γ_C`. Repeated comparisons for any finite family of upper sets agree as actual coordinate maps, independent of the parenthesization.

**Proof.** A compatible pair agrees exactly on the overlap. Its inverse assigns to each coordinate in the union the value from either containing set, which is well-defined. Naturality follows from Theorem 2.1. With three or more sets, every association produces the same named coordinate at every occurrence; repeated coordinates are constrained equal, not independently sampled. This proves the stated coherence. QED.

If `ρ` is a common learned joint state or finite-path law, equip the tuple object with `(Φ_{I,J})_*ρ_{I∪J}`. Then `Φ` is measure-preserving by construction. This measure is **not** in general the independent fibre-product coupling of `ρ_I` and `ρ_J`. The theorem preserves the given positive joint process rather than inventing one from separately plausible marginals.

For each preorder block `B`, set `U_B=↑B\B`. Both `U_B` and `U_B∪B` are upper. The projection

\[
 X_{U_B\cup B}\longrightarrow X_{U_B} \tag{2.2}
\]

is a conditional component fibre object, and `c` induces a fibre diffeomorphism over `c_{U_B}`. This is the mathematically correct sense in which a block can be identified as a fibre over an invariant base even if its standalone chart is not fixed.

### Exact relation to the original witness machinery

The maps in (2.1) are explicit named-coordinate bijections. For actual one-step records, apply them to **both** source/target state coordinates and event coordinates, while retaining actions, observations and every named noise/event occurrence. A valid graph-map comparison then has the shape required by `Assignment.operationEquiv`; exactness requires the resulting state and event maps to be bijections. Empty profiles retain their actual interface object. Equality of all such map interpretations is still needed for `EquationMaps` before invoking `presentedExtend`.

This supplies a concrete candidate assignment/comparison, not a proof that every historical presentation equation holds for it. Nor is (2.1), a set-theoretic overlap square, automatically a physical causal adapter. The operational and probability-bearing checks of the companion weighting note remain necessary.

## 3. Why invariant state interfaces are not yet local mechanisms

The preorder (1.1) concerns coordinate gauge preservation, **not** temporal causal dependence. For a Markov kernel `K`, an autonomous quotient through `π_I` exists only if

\[
 K(z,\pi_I^{-1}(E))=\bar K(\pi_I z,E)
 \quad\text{for all }z,E. \tag{3.1}
\]

An invariant `I` need not satisfy (3.1). For example, with temporal adjacency

\[
 G^z=\begin{pmatrix}1&1\\0&1\end{pmatrix},
\]

the intersection of row- and column-inclusion preorders is the identity, so each singleton coordinate interface is invariant. Yet a first coordinate transition depending genuinely on the previous second coordinate is not autonomous. It needs that previous coordinate (or an exact sufficient physical port) as a temporal boundary input.

A fibre construction can avoid falsely requiring autonomy by retaining every actual temporal parent input and observation-generation dependency. Finite resource bounds then additionally require a justified finite memory order or recursively realizable finite statistic, not access to arbitrary entire histories. A coordinate base used only to describe a change of chart is not automatically a robot communication port. Conversely a physical device cannot use a hidden base merely because it is available in the proof diagram.

## 4. Actual residual mixing is controlled by common kernel symmetries

The following statement uses the **actual positive conditional mechanisms**, not only their graph.

Let blocks be ordered with strict upper blocks first. Let `c` be a `C¹` block-triangular diffeomorphism on the product of Euclidean block spaces. For each conditioning context `h` in a specified family, suppose the input and output current-state distributions are both products across blocks:

\[
 \mu^h=\bigotimes_B\mu_B^h,
 \qquad c_*\mu^h=\nu^h=\bigotimes_B\nu_B^h. \tag{4.1}
\]

Each measure has a positive density on its entire Euclidean space. In the latent dynamic application, `h` includes the old latent history and auxiliaries; the target context is its correctly transformed history. That relabeling is held fixed while varying the **current** base `u`, and is suppressed in `ν_B^h`.

For fixed block `B` write the fibre map as `T_u(x)=c_B(x,u)`, where `u∈X_{U_B}`. Each `T_u` is a diffeomorphism. Choose one reference `u_0` and write

\[
 R_u=T_{u_0}^{-1}\circ T_u. \tag{4.2}
\]

### Theorem 4.1 — exact common-symmetry condition

Under (4.1),

\[
 (T_u)_*\mu_B^h=\nu_B^h
 \quad\text{and}\quad
 (R_u)_*\mu_B^h=\mu_B^h
 \qquad\text{for every }u,h. \tag{4.3}
\]

Conversely, for a block-triangular map, if each block fibre transports its source conditional factor to its required target factor independently of the current base as in (4.3), then it transports the full product law to the full target product law. Thus, once a reference block transport is fixed, admissible base dependence is exactly a family in the **common symmetry group**

\[
 \operatorname{Aut}(\{\mu_B^h\}_h)
 =\bigcap_h\{R:R_*\mu_B^h=\mu_B^h\}. \tag{4.4}
\]

**Proof.** The upper-set map `c_{U_B}` is invertible. Conditioning the target product law on `Y_{U_B}=c_{U_B}(u)` leaves the `B`-law equal to `ν_B^h`. Conditioning the source product law on `X_{U_B}=u` leaves its `B`-law equal to `μ_B^h`; its transformed value is `T_u(X_B)`. This proves the first identity for almost every `u`. For bounded continuous test functions, the transformed expectations depend continuously on `u` by dominated convergence. Full support of the base density upgrades almost-everywhere equality to all `u`. Composing with `T_{u_0}^{-1}` proves the second identity. Conversely, sample upper blocks first. At each step the conditional distribution of the next transformed block is its specified `ν_B^h`, independent of all earlier transformed blocks, so the resulting law is their product. QED.

The converse here is about current conditional laws. To define an actual alternative dynamic model the same `c` must transport **every** temporal conditional kernel and initialization, and the transformed histories and allowed graph must be checked. Preserving one marginal does not establish dynamic observational equivalence.

### Corollary 4.2 — scalar fibre rigidity

If block `B` is one-dimensional and its base is connected, `T_u` is independent of `u`. Thus if all preorder blocks are scalar, any actual smooth product-law equivalence with that preorder support is componentwise, after the aligned permutation.

**Proof.** `R_u` is a continuous family of scalar diffeomorphisms starting at the identity. Its derivative cannot vanish, and its orientation cannot change on a connected base. It is therefore increasing. An increasing diffeomorphism preserving a full-support scalar probability measure satisfies `F(R_u(x))=F(x)` for the strictly increasing cumulative distribution function `F`; hence `R_u(x)=x`. QED.

The scalar fibre argument has explicit causal-representation-learning antecedents: **Brehmer–de Haan–Lippe–Cohen (2022), supplementary Lemma 2**, proves constancy of a differentiable family of scalar transports ([published supplement, §A.2](https://papers.nips.cc/paper_files/paper/2022/file/fa567e2b2c870f8f09a87b6e73370869-Supplemental-Conference.pdf)); **Liang et al. (2023), Causal Component Analysis, proof of Theorem 4.2(ii)**, uses that lemma with triangular marginal transport to remove off-diagonal dependence ([published paper, pp. 19–21](https://proceedings.neurips.cc/paper_files/paper/2023/file/67089958e98b243d5cc1881ad60418b8-Paper-Conference.pdf)). **Xi–Bloem-Reddy (2023), Proposition 5.2 and Appendix E.1**, gives the triangular nonlinear-ICA componentwise-identification corollary for full-support independent latent distributions ([primary text](https://arxiv.org/html/2206.00801v5#S5.SS1)). Here the triangular restriction is on the source consistency **residual map**, rather than on the emission maps; fixed orientation flips reduce it to their monotone triangular product-transport argument. The direct proof above retains explicit global invertibility, connected-base and full-support hypotheses and permits atoms. The distinct-signature consequence is a source-specific combination with these established rigidity arguments, not a new scalar transport theorem or an established priority claim. See `Rigidity_Prior_Art_Comparison.md` for the exact comparison and search limits.

On a circle, discontinuous/modulo maps, disconnected domains or a discrete finite base, the stated proof need not apply. No claim is made that the continuous conclusion automatically solves the finite-state contract.

**Explicit false-positive envelope example.** Two independent unit Gaussians and the support-allowed shear `(x,y)↦(x+y,y)` have correlated output with covariance one. The shear lies in a triangular sparsity envelope but does not transform that product law to a product law. It is therefore not an admissible alternative within the source's no-instantaneous-dependence model class. Rejecting it does not reject the original learned decomposition.

### Corollary 4.3 — likelihood-ratio rigidity in any block dimension

Assume the factor densities `p_B^h` are positive and `C¹`. Fix `h_0`. Suppose, at every `x`,

\[
 \operatorname{span}\left\{
 \nabla\log\frac{p_B^h}{p_B^{h_0}}(x):h\right\}
 =\mathbb R^{|B|}. \tag{4.5}
\]

Then `T_u` is independent of `u` on a connected base.

**Proof.** Since `R_u` preserves every factor measure, dividing the change-of-variable identities for `h` and `h_0` cancels the Jacobian and gives

\[
 \frac{p_B^h}{p_B^{h_0}}(R_u(x))
 =\frac{p_B^h}{p_B^{h_0}}(x).
\]

Differentiate along any differentiable base path `u(s)`. The velocity `dR_{u(s)}(x)/ds` is orthogonal to all log-ratio gradients at `R_{u(s)}(x)`. By (4.5) it vanishes. Connected Euclidean bases are path connected, and `R_{u_0}=id`, so every `R_u=id`. QED.

This is a checkable **sufficient** rigidity certificate, not an iff criterion: a family may have no nontrivial smooth common symmetry even when the displayed gradient span is deficient. It is also invariant under a common block diffeomorphism, since likelihood ratios compose and their differentials transform by an invertible Jacobian. The completed source implication is proved in `Residual_Transport_Rigidity.md`, §7, and checked in `Final_Residual_Review.md`: the applicable S26 auxiliary or temporal influence condition removes strict-base dependence into an SCC with the corresponding nonempty incoming-parent set. That proof uses dense local likelihood-ratio rank with positive witness neighborhoods, not the stronger everywhere-positive version of (4.5) displayed here. Singleton SCCs need only one transported full-support product initialization; parentless multidimensional SCCs can remain nonrigid.

### Genuine nonrigid alternative

For a two-dimensional block with isotropic centered Gaussian factors `N(0,σ_h² I₂)`, all rotations preserve every factor. Therefore

\[
 T_u(x)=R_{\phi(u)}x
\]

can vary smoothly with a current scalar base `u` while preserving all these conditional product laws. This is an actual static product-law ambiguity, not just a support-allowed shear. It extends to a dynamic family if the block conditional variances and every other mechanism depend on prior block values only through rotation invariants and all initialization/emission maps are transported consistently. Such a family can have interacting radii, but no claim is made that it satisfies the published sufficient-variability hypotheses. Indeed those hypotheses may exclude its symmetry. This example establishes the exact obstruction to removing the conditional base without an additional rigidity condition.

### Finite-state analogue: exact symmetry signatures

For a finite block state set `X_B` and a family of positive probability vectors `p_B^h`, a permutation preserves every vector exactly when it permutes only states with identical signatures

\[
 x\longmapsto(p_B^h(x))_h. \tag{4.6}
\]

Thus the common permutation symmetry group is the product of symmetric groups on equal-signature classes. Distinct signatures force trivial base dependence even on a discrete base; repeated signatures permit base-dependent fibre permutations. This is a finite exact computation from learned kernel tables, not a finite-state latent-learning theorem. The dynamic alternative still has to preserve all transformed-history mechanisms.

## 5. What this route adds, and what remains

### Added beyond citing consistency alone

- An explicit invariant interface lattice and conditional fibre objects constructed from the **learned** residual preorder;
- exact overlap/refinement coordinate maps retaining a common root process;
- an exact reduction of actual base-dependent mixing to common symmetries of the learned conditional factors;
- scalar and likelihood-ratio rigidity tests that can remove apparent ambiguity permitted by the graph envelope;
- explicit failure of the inference “gauge-invariant interface means autonomous local component.”

### Not yet established

The bundle projection alone does not derive a physical port allocation. It has no permission to send hidden base values to robot controllers. It does not make all identified fibres dynamically closed, solve global observation generation, or prove finite memory for the source's non-Markov history kernels. Section 6 supplies a separately restricted direct-port admission theorem after scalar rigidity; it does not remove these limits in general. Demanding invariant standalone physical components under every envelope gauge would be an artificial strengthening: a candidate decomposition may legitimately choose a learned representation and retain other alternatives by explicit coordinate transport.

For a deployment theorem, one must first say whether an interface is (i) a proof chart, (ii) a persistent hidden environment coupling, or (iii) physically acquired controller information. Different roles have different resource implications. A port obstruction based only on failure of envelope invariance is not a physical impossibility theorem.

The main missing theorem remains the contract-strength finite-state/finite-resource discovery theorem beyond automatic latent-factor assembly. Section 6 gives a growing continuous raw-port class with an exact allocation criterion, but its normalization is inherited from the learner and its resource grammar is narrow. The present results shrink/organize residual ambiguity before more general synthesis and diagnose omitted causal inputs. They do not by themselves meet the stronger synthesis gate.

## 6. A growing same-baseline-access strictness family

This section gives a concrete growing family for the scalar residual sharpening, and an exact resource-admission theorem in a deliberately specified **continuous raw-analog-port class**. It is not a finite-state theorem or a new general structured-realization result.

### 6.1 Interacting Gaussian path with nonlinear noisy local readouts

For each `n≥3`, let `G_n` be the symmetric nearest-neighbor path adjacency including every self-loop. There are `m=3n−2` directed allowed edges. Assign different exponents `k_e=1,…,m` to these edges, and define

\[
 A(a)_{ij}=\begin{cases}a^{k_{ij}},&(j\to i)\in G_n,\\0,&\text{otherwise}.\end{cases}
\]

Use a scalar observed auxiliary `a`, independent unit Gaussian innovations, product standard Gaussian initialization, and

\[
 Z^t=A(a^{t-1})Z^{t-1}+\eta^t.
\tag{6.1}
\]

No stability or infinite-time bounded-variance assertion is made; every finite horizon defines a normalized positive law. For readouts take cyclic indices and

\[
 f_i(z)=z_i+\epsilon\tanh(z_{i+1}),\quad 0<\epsilon<1,
 \qquad X^t=f(Z^t)+\xi^t,
\tag{6.2}
\]

with independent Gaussian observation noise of the fixed known variance required by the source. The map `f` is a smooth diffeomorphism: for every `x`, the equation `z=x−εtanh(Sz)` has a unique solution by contraction; `Df=I+εDS` is invertible since `||εDS||<1`, giving a smooth inverse. Thus each readout is a genuine noisy mixture of two latent coordinates, not an exact local decoder.

**Source hypothesis check for temporal influence.** The mixed current/past Hessian of the conditional log density is `A(a)`. At a fixed current `z`, the source's constraint that the selected past state equal that same `z` does not affect this Hessian. Taking `m` different positive auxiliary values gives coefficient vectors `(a,a²,…,a^m)` with invertible Vandermonde matrix. Their Hessians therefore span the full `G_n`-supported matrix space. Smoothness, full support and conditional coordinate independence hold. Consequently, subject to the source's remaining declared population assumptions and a learned graph no denser than the true one, its temporal consistency conclusion applies for `T≥2`.

Every closed-neighborhood row of `G_n` is distinct, so its combined row/column inclusion preorder has only singleton blocks. Yet the first endpoint's neighborhood is properly contained in the second vertex's neighborhood, and likewise at the other end. The source's displayed graphical criterion for complete disentanglement therefore fails. Corollary 4.2 nevertheless upgrades the triangular consistency conclusion to componentwise equivalence after permutation. This shows a strict improvement over that particular sufficient graphical criterion on a growing interacting family, while crediting the standard transport uniqueness that makes the improvement possible.

It is not a claim that the authors' full results or all prior ICA results fail to imply this improvement by other routes. Such a comparison needs a separate literature/theorem audit.

### 6.2 Exact raw-port admission after rigidity

Freeze the following physical model class independently of the learned allocation:

An intended application is modeling a pre-existing modular analog plant with known available wiring, fixed one-step deadlines and one persistent physical state variable per module, where adding stores, relays or sensor preprocessing is outside the allowed hardware class. These restrictions must come from that independent specification; they are not universal physical laws and should not be introduced solely to manufacture the obstruction below.

- `n` named slots, each owning one scalar hidden state and its private fresh innovation;
- stationary first-order mechanisms with no additional hidden stores;
- a declared directed graph `H` of permitted **physical environment** couplings, carrying the previous scalar state from sender to receiver with the required one-step timing; include every self-loop as bookkeeping for the slot's own state, which is already locally available and is not charged as inter-slot communication;
- specified admissible auxiliary input lines;
- each named output sensor `j` has a specified allowed set `F_j` of current hidden-state slots and fresh local readout noise;
- no within-tick relays, hidden central decoder, or extra state duplication beyond these declared ports.

The physical slot assignment of learned factors is **not** supplied. These are analog scalar ports, not finite-bit communication links and not a declaration that a robot senses latent states. The grammar is a restricted direct-coupling realization class; a richer implementation might defeat its obstructions. Candidate latent models also retain the source theorem's regularity, latent-dimension, observation-model and population sparsity-cap assumptions. In particular, the temporal graph must be no denser than the graph against which source identifiability is invoked. A hardware graph permitting additional wires does not license dropping this statistical model-class condition.

For the learned model, determine its *essential* first-order kernel dependencies `E_dyn` and essential sensor dependencies `E_obs`: an edge is present exactly when changing that argument while holding the other admissible arguments fixed can change the conditional law. For additive fixed Gaussian readout noise, sensor dependence is equivalently essential dependence of its mean `f_j`. Record essential auxiliary dependencies similarly. This is an exact mathematical object; an executable end-to-end algorithm additionally needs a symbolic representation or certificates/oracles for essential-dependence tests. Arbitrary black-box real functions do not supply decidable equality tests for free. In the displayed Gaussian/analytic family the required supports have explicit formulas, and the source graph theorem supplies the temporal support up to alignment.

### Theorem 6.1 — finite placement criterion for this class

Assume all observationally equivalent admissible `n`-scalar source models are componentwise/permutation equivalent, as established above for the named family. Quantify realizations over the **intersection** of the frozen direct-coupling slot grammar and the identifying source universe: same latent dimension, stationary first-order conditionally independent latent transitions, source-compatible diffeomorphic emission with the fixed additive Gaussian noise model, regularity/full support, and the identifying graph sparsity cap. A realization in this intersection exists if and only if there is a bijection `π` from learned scalar coordinates to slots such that:

1. every `k→i` in `E_dyn` maps to an allowed coupling `(π(k),π(i))` of `H`;
2. every `k→sensor j` in `E_obs` satisfies `π(k)∈F_j`;
3. all essential auxiliary inputs have the allowed lines to the corresponding slots.

For every such `π`, copying the learned scalar kernels and sensor kernels to those slots and using the indicated actual wires constructs a positive realization of the **same** process. All admissible placements can be retained as explicit alternatives. Failure of the finite placement test rules out this entire identified-model/direct-port class, not just one arbitrary learned coordinate gauge.

**Proof.** Essential dependence is invariant under invertible componentwise reparameterization: two argument values witnessing dependence map to two such values after the reparameterization, and invertible output reparameterization preserves inequality of conditional measures. The same argument applies to observation means/distributions. Permutations only relabel vertices. Thus every equivalent source model has exactly these dependency relations up to one permutation.

Necessity follows because a slot's mechanism in the declared grammar is a function/kernel only of its own state, its incoming raw states and available auxiliaries. An essential missing argument cannot be reconstructed by a relay, extra store or decoder because those resources are expressly absent. A named sensor likewise uses only `F_j`.

For sufficiency, place the learned factors by `π` and supply each essential argument on its permitted wire. Sample every private innovation once; sample sensor noise only at its named sensor. The learned conditional factors are already nonnegative and normalized, and their initialization and repeated transition product are exactly the learned law. No extra positivity or compatibility assumption is invented. The learned observation kernel is reproduced by its actual local generating factors, not by inverse decoding. This gives the claimed common process. QED.

After essential supports are certified, the test is ordinary finite constrained graph/hypergraph placement; it may be expensive (a direct search checks at most `n!` placements). Its gain here is that conditional-product rigidity removes an uncountable latent-coordinate realization search and makes the obstruction valid across the **actual** identified equivalence class inside the sparsity-capped source universe. It is not an invention of graph embedding, nor a replacement for structured realization in more expressive or denser latent classes.

The family (6.1)–(6.2) fits a cycle of scalar hidden-state slots with nearest-neighbor physical couplings and two-adjacent-state sensors, after discovering a compatible placement. Each hidden transition has at most three old-state arguments, each sensor two current-state arguments, and the total used temporal/sensor wires is at most `(3n−2)+2n=5n−2`. There are `n` hidden scalar stores and `n` scalar readouts. An auxiliary delivered to all slots has `n` charged input incidences; it is not a free robot broadcast. The nonlinear map and noisy observations do not reveal exact hidden states at runtime.

The own-state terms in that upper bound are local argument incidences, not inter-module communication; excluding them leaves at most `4n−2` temporal/sensor signal incidences. The explicit polynomial representative has exponents at most `3n−2`, a description of size `O(n log n)`, and each local mean in that representative can be computed with `O(log n)` multiplications using local exponentiation by squaring for its at-most-three monomials. These arithmetic bounds are **not gauge invariant**: an arbitrary learned componentwise diffeomorphism can make the actual formulas/samplers much more expensive. The theorem bounds scalar-store and port incidences only; actual learned code, sampling, offline preprocessing and precision costs must be reported separately. It does not promise a cheap gauge-normalization procedure, and an additional finite computation budget would need another admissibility test. There are `n` latent innovation draws and `n` observation-noise draws per step in the polynomial representative. This is real-arithmetic/analog accounting, not a finite-bit, precision, energy or fabrication guarantee. The polynomial auxiliary dependence is a designed identifiability stress family, not a validated robot or thermal model.

**Matched explicit obstruction.** Keep the same statistical model class, slot count and no-relay/no-extra-state grammar, but require each named sensor to access at most one hidden slot. Every mean `f_j(z)=z_j+εtanh(z_{j+1})` has two essential latent arguments. Componentwise/permutation equivalence preserves that number. Hence no placement passes condition 2, so this sensor class cannot realize the same learned law. Allowing two adjacent scalar inputs repairs it by the preceding construction. This is an obstruction to observation **generation** under a specified physical class, not to decoding a latent state from noisy readouts, and not an impossibility for architectures with extra preprocessing, different latent dimension or models outside the sparsity-capped source universe.

The resource result compares conditional laws for the declared auxiliary-input sequences. Treating that auxiliary as an intervention chosen by a controller requires the separate causal-access and coverage assumptions; observation of `a` alone does not supply them. Temporal extrapolation also uses the frozen stationary first-order model class: within that class, equality/transport of the initial law and one full-support transition identifies its repeated use. A finite-horizon source theorem without that restriction would not certify arbitrary later-time kernels.

This is an explicit positive growing construction and a matched class-relative obstruction. Nevertheless, its positive stochastic assembly is already supplied by the joint learner and conditional independence, and its resource grammar uses direct raw analog state couplings. It should be reported as a **scoped learned-model-to-port admission bridge**, not as satisfying the stronger finite-state O2 acceptance gate or solving unknown noisy finite-message architectures.

### 6.3 Coherence retained, limits retained

Within the rigid class all coordinate subsets are preserved by residual componentwise maps. The overlap comparisons of §2 therefore apply to every coordinate cut, and grouped views/refinements can retain exact named joint-state/event records. Component grouping or a coordinate cut does not authorize an unavailable physical wire. Arbitrary nonbijective stochastic interface changes still have the normalization and record-multiplicity issues proved in `Typed_Realization_Bridge.md`; the growing family does not settle full equipment closure.

## 7. Comparators and claim discipline

The graph-preserving group and consistency upper bound are already in Lachapelle et al. The coordinate-preorder diagram is a direct structural construction from that result. Its crossing comparison is the ordinary product-coordinate pullback, now explicitly aligned with retained witness records; no new pullback theorem is claimed.

Scalar rigidity has the direct antecedents credited after Corollary 4.2: Brehmer et al. (2022), supplementary Lemma 2; CauCA (2023), proof of Theorem 4.2(ii); and Xi–Bloem-Reddy (2023), Proposition 5.2 and Appendix E.1. General monotone triangular transport uniqueness is also treated by Baptista–Morrison–Zahm–Marzouk, *Learning non-Gaussian graphical models via Hessian scores and triangular transport*, §3.1 ([primary JMLR paper](https://www.jmlr.org/papers/volume25/21-0022/21-0022.pdf)). The completed bounded comparison in `Rigidity_Prior_Art_Comparison.md` distinguishes these established mechanisms from the checked source-specific distinct-signature consequence. Its strictness is relative to the source's displayed graphical sufficient criterion, not every result in the literature; priority remains unestablished.

The likelihood-ratio symmetry test is elementary common-measure invariance, related to sufficient-statistic and nonlinear-ICA variability arguments. CauCA Corollary 4.8, via Theorem 4.5 and its block score-discrepancy assumption, is a close influenced-block comparator, but its known intervention-target setting does not itself verify the S26 residual-preorder and history obligations. Those source-specific implications are now proved in `Residual_Transport_Rigidity.md`, §7, and independently checked in `Final_Residual_Review.md`. Their use here is rigorous conditional sharpening, with scientific priority unresolved; see `Rigidity_Prior_Art_Comparison.md`.

The original `Calc` integration is only as strong as the supplied actual state/event maps, probability transport and presentation equation checks. Ordinary bundle notation alone neither provides an operational decomposition nor closes the equipment/interface-change obligations.

Exact structural regressions are in `verify_residual_fibre_family.py` and `Residual_Fibre_Family_QA.json`. For `n=3,…,8` they verify singleton residual SCCs with strict order pairs, the full monomial-Hessian Vandermonde determinant, and embedding of the dynamic/sensor dependencies into cycle raw ports. They are finite tests of formulas, not a replacement for the all-`n` proof or the source theorem.
