# Learned positive models to typed realizations: exact boundary and unresolved main theorem

**28 October 2026. Status: a scoped continuous identifiability-to-port bridge plus rigorous supporting obstruction/repair results. The stronger finite-state discovery completion theorem is NOT established.** The detailed main-route construction and proofs are in `Residual_Fibre_Interface_Candidate.md`; they are not replaced by the diagnostics in this file.

## New main-route result after the initial diagnostic

The residual-consistency route now provides the following **scoped admission theorem**, independently reviewed at its stated boundary.

Assume an actually learned first-order positive latent model satisfies the continuous source-identifiability hypotheses, and the resulting residual support preorder has singleton strongly connected classes. Because both true and learned current conditional laws are product measures, the residual triangular diffeomorphism is componentwise after permutation: scalar monotone transport uniqueness removes the strictly triangular entries permitted by the graph envelope. This credits a standard Knothe–Rosenblatt mechanism and does not claim new transport theory.

Freeze independently an `n`-slot direct analog-coupling grammar: one scalar hidden state per slot, specified previous-state environment wires and current-state sensor inputs, specified auxiliary lines, no additional stores/relays. Restrict candidate realizations to its **intersection with the identifying source universe**, including the same dimension, first-order stationary conditional-product laws, diffeomorphic additive-known-noise emission assumptions and identifying sparsity cap. Then a positive realization exists **iff** a bijection from learned scalar factors to slots sends every essential learned transition, sensor and auxiliary dependency to an allowed input. The allocations and actual used ports are outputs.

**Proof mechanism.** Componentwise invertible maps preserve essential argument dependence, so the learned dependency graph is valid across the actual identified equivalence class, not merely one chart. A physical mechanism missing an essential argument cannot realize its conditional law in the no-relay/no-extra-store grammar. Conversely any admissible placement directly installs the already-normalized learned mechanisms and local observation generators, with their original initialization and one sampling occurrence per factor. This reproduces one common process. The search is ordinary finite constrained graph placement after essential supports are certified; arbitrary real-function dependency extraction is not free.

A growing interacting Gaussian path family with monomial auxiliary modulation satisfies the source's temporal Hessian-span condition by an exact Vandermonde argument. Its graph has singleton residual blocks but strict neighborhood inclusions, so the displayed source graphical criterion fails even though the sharpened scalar-rigidity argument establishes componentwise identification. Noisy nonlinear local mixing `f_i(z)=z_i+εtanh(z_{i+1})`, `0<ε<1`, is globally diffeomorphic and uses two latent inputs per sensor. The model admits `O(n)` scalar stores/signal incidences on a cycle; sensors restricted to at most one latent input fail for the whole identifying/direct-port class, while two adjacent inputs give the positive construction. This is about observation generation, not exact hidden-state decoding. The all-`n` argument and exact finite structural regressions are in the companion note and QA files.

The same note constructs invariant upper-set interfaces and SCC conditional fibre objects for the nonrigid case, with exact natural coordinate-overlap comparisons preserving the learned common law. Actual base-dependent fibre transformations must lie in common symmetries of the conditional kernel family; scalar or likelihood-ratio-rigid fibres eliminate them. Nontrivial unactuated multidimensional rotational symmetries remain possible, so a universal collapse to blockwise physical components is not claimed.

**Remaining scope boundary:** this is a continuous direct-analog-port admission/ambiguity result, not finite-state or finite-bit discovery, general structured-network realization, finite-data inference, arbitrary stochastic equipment closure, or a claim of O2 completion. The latent learner already supplies the positive assembly; the added content is the residual-class sharpening and its class-wide placement/obstruction consequence.

## Results first

The latent learner's output must be credited as a positive construction. A successfully learned collection of normalized conditional latent kernels and an observation kernel already defines one temporally consistent positive process. It is not merely a signed predictor awaiting an unspecified positivity miracle. If the permitted component/interface universe accepts those very factors and their dependencies, this can already be a solution; there is no legitimate reason to make assembly artificially hard.

The remaining burden is conditional on independently motivated restrictions: allowed physical mechanism placements, causal access and timing, local memory, particular physical ports, observation generation, shared randomness and robot communication. None of these restrictions can be inferred just by treating every latent edge as a robot message. Hidden component state need not be decoded from current observations. A noisy emission map is not a runtime inverse.

The exact bridge investigated here exposes a separate, concrete obstruction in the original witness machinery:

1. A normalized output lift along a finite interface map exists exactly when every used coarse output has a preimage. All such lifts require a conditional probability law on each used fibre.
2. **There is no contravariantly compositional assignment of stochastic sections to all finite surjections.** This is not merely lack of a preferred uniform formula: symmetry and a three-to-two-to-one chain give a contradiction for any such assignment.
3. Compatible positive interface measures repair nested composition by Bayesian sections. This is established Bayesian-inversion machinery, not a new discovery principle. It narrows interface changes, needs additional probabilistic data, and does not supply cartesian universality among all lifts.
4. Probability-preserving stochastic refinement is not an exact actual-record refinement. A two-element fibre can preserve total probability while its forgetful map fails the original event-bijection test.
5. A fixed boundary distribution is not enough for reuse through time. A single causal lifting table must intertwine **every action/outcome instrument**, not only the observation-averaged transition. The exact finite criterion and a strictly positive noisy hidden-state counterexample are below.

The diagnostic results below identify requirements for a valid bridge; by themselves they do **not** construct unknown resource-bounded component assignments. The subsequently developed continuous direct-port theorem above gives a scoped growing-family construction, not the stronger finite-state target. Rebranding known profile quotients, finite-state minimization, junction-tree assembly, or generic parameter enumeration would not fill that remaining gap.

## 1. Scope, source and access contract

### 1.1 The learned object is an intermediate output, not an oracle input

The companion `Baseline_Translation.md` translates Lachapelle et al. CLeaR 2022 and arXiv:2401.04890v2. Its relevant population output has the form

\[
 p(z^{1:T},x^{1:T}\mid a^{<T})=
 \prod_{t=1}^{T}\prod_i p_i(z_i^t\mid z_{\mathrm{pa}_i}^{<t},a_{\mathrm{pa}_i}^{<t})
 \prod_{t=1}^{T}e(x^t\mid z^t).
\]

The published source is continuous, permits history dependence, and has specific population-identifiability assumptions. Its initialization and equivalence conventions must be taken from the exact translated theorem, not silently replaced by arbitrary correlated initialization or finite-state Markov assumptions. Its emission is noisy. The identified graph and kernels can be real discovery outputs, not supplied charts. Exact observational equality in that theorem is not a finite-data learning guarantee, and observed auxiliary variables are not automatically randomized causal interventions.

**All formal results below are finite-set statements.** They can be applied to a finite positive model once learned under a separately justified finite-state theorem, or used as finite obstructions to a proposed semantics. They are not a finite-state corollary of the continuous nonlinear-ICA theorem. No revealing reset, state decoder or extra experiment is introduced here.

### 1.2 Original machinery actually inspected

The unchanged original dynamic target uses `Assignment.calculus` and retains all boundary-compatible graph maps, with exactness marked by `Graph.IsIso` on states **and actual events**. Relevant source APIs are:

- `WitnessedDecompositions/Dynamic/Target.lean`: `Op.witness`, `Op.Exact`, `operationEquiv`, and the nullary exactness/common-leg theorems;
- `WitnessedDecompositions/Dynamic/Bridge.lean`: `GeneratorMaps`, `EquationMaps`, `freeExtend`, `presentedExtend`, `descends_iff`, and `presentedRefinementFunctor`;
- the original occurrence substitution uses `Path.Slot` / `Path.slotExpand`, not a replacement untyped syntax;
- `GraphSpanModel.md` in the previously delivered structural source archive, §§4 and 9: all-interface witnessed pullbacks and the exact fibre of the internal base-change comparison.

The graph-span restriction retains every preimage record. Section 9 explicitly computes the fibre of the forgetful comparison as `g^{-1}(b)`. That is precisely the record-level calculation used below. The graph coordinate and original global monoid decoration remain separate from probabilities; arbitrary scalar decorations are not probabilities and cannot be renormalized away.

## 2. Exact normalized-lift criterion

All matrices act on probability row vectors on the right. A function is identified with its zero-one row-stochastic matrix. Let

\[
 K:A\rightsquigarrow B,\qquad f:A'\to A,\qquad g:B'\to B
\]

be finite, with `K` row-stochastic. Write `F,G` for the function matrices. We seek a row-stochastic `K':A'⇝B'` satisfying

\[
 K'G=FK. \tag{2.1}
\]

This equation says that forgetting the fine output recovers exactly the specified coarse output law for every retained input. It is a probabilistic lifting question, not a claim that this is already a cartesian cell in an equipment.

### Theorem 2.1 — existence and all lifts

Such a `K'` exists if and only if

\[
 K(b\mid f(a'))>0\ \Longrightarrow\ g^{-1}(b)\ne\varnothing
 \quad\text{for all }a',b. \tag{2.2}
\]

Every lift is exactly of the form

\[
 K'(b'\mid a')=K(g(b')\mid f(a'))\,
 \lambda(b'\mid a',g(b')), \tag{2.3}
\]

where, for each used positive-mass pair `(a',b)`, `λ(·|a',b)` is a probability distribution on `g^{-1}(b)`. No distribution is required on an empty, zero-mass fibre. Choices on nonempty zero-mass fibres are irrelevant to `K'`.

**Proof.** Summing a putative lift over `g^{-1}(b)` gives (2.1); an empty fibre cannot supply positive mass. Conversely, choose a distribution on each nonempty used fibre and apply (2.3). The mass in each coarse fibre is the required `K(b|f(a'))`, so rows sum to one and (2.1) holds. For any lift and any positive-mass pair, divide `K'(b'|a')` by `K(b|f(a'))` to recover the unique corresponding conditional distribution. Nonnegativity forces all entries over a zero-mass pair to vanish. QED.

**Immediate obstruction.** Let `A` be a singleton, `B={0,1}`, `K=(1/2,1/2)`, and let `g:{0}→B` select zero. No normalized lift exists. Renormalizing the surviving half changes the law; adding a failure output changes the interface and process specification. Empty output fibres are therefore not merely a notational difficulty.

**What this does not prove.** It does not show that no suitable ambient probabilistic equipment can exist. It shows that one cannot simply take all normalized kernels, retain the original arbitrary deterministic interface maps, and assert that the original witnessed pullback formula remains normalized and law-preserving. An ambient nonnegative/unnormalized semantics with a separately checked normalized operational class remains possible.

## 3. No coherent normalized sections for naked finite surjections

A stochastic section of a surjection `g:X→Y` is a stochastic matrix `S_g:Y⇝X` supported on its fibres, equivalently `S_g G=I_Y`. For a bijection it is necessarily the deterministic inverse.

### Theorem 3.1 — no functorial splitting on all finite surjections

There is no assignment `g↦S_g` of stochastic sections to **all** surjections between nonempty finite sets such that

\[
 S_{g\circ h}=S_g S_h \tag{3.1}
\]

for every composable `h:X''→X'`, `g:X'→X`.

**Proof.** For the unique map `r_X:X→{*}` and any permutation `σ` of `X`, `r_X∘σ=r_X`. A section of a bijection is its inverse, so (3.1) forces `S_{r_X}=S_{r_X}σ^{-1}`. Thus `S_{r_X}` is uniform on `X`.

Let `h:{0,1,2}→{u,v}` send zero to `u` and one,two to `v`; let `g:{u,v}→{*}`. The preceding argument makes `S_g=(1/2,1/2)` and `S_{g∘h}=(1/3,1/3,1/3)`. Since `h` is unchanged by swapping one and two, the same compositional argument forces the `v`-row of `S_h` to be uniform on `{1,2}`, while its `u`-row is concentrated at zero. Consequently

\[
 S_g S_h=(1/2,1/4,1/4)\ne(1/3,1/3,1/3)=S_{g\circ h},
\]

contradicting (3.1). QED.

No extra equivariance axiom is needed: compositionality with bijections already forces it. The theorem concerns normalized sections with fixed endpoint sets and ordinary composition. It is not a theorem that all possible stochastic double-category constructions fail.

## 4. A measured repair, and exactly what it repairs

Let an interface carry a strictly positive probability vector. Restrict vertical changes to functions

\[
 g:(B',\beta')\longrightarrow(B,\beta),\qquad \beta'G=\beta.
\]

Such a map is necessarily surjective. Define the Bayesian section

\[
 S_g(b'\mid b)=\mathbf1_{g(b')=b}\frac{\beta'(b')}{\beta(b)}. \tag{4.1}
\]

### Proposition 4.1 — normalized nested repair

`S_g` is stochastic, `S_gG=I`, and `βS_g=β'`. For compatible measured maps `h` then `g`,

\[
 S_{g\circ h}=S_gS_h. \tag{4.2}
\]

If `K:(A,α)⇝(B,β)` satisfies `αK=β`, and `f:(A',α')→(A,α)` is measure-preserving, then

\[
 R_{f,g}K=FKS_g \tag{4.3}
\]

is normalized, transports `α'` to `β'`, and satisfies `(R_{f,g}K)G=FK`.

**Proof.** Summing (4.1) over a fibre yields one; the other two identities follow directly. For (4.2), there is exactly one compatible intermediate point `b'=h(b'')`; the product of the two ratios telescopes from `β'(b')/β(b)` and `β''(b'')/β'(b')` to `β''(b'')/β(b)`. Finally `α'FKS_g=αKS_g=βS_g=β'`; row normalization and the projection identity follow from stochastic composition and `S_gG=I`. QED.

This is finite Bayesian inversion with fixed positive priors. It is known machinery: see Braithwaite–Hedges–St Clere Smithe, *The Compositional Structure of Bayesian Inference*, Proposition 21 and Remark 23, and Cho–Jacobs, *Disintegration and Bayesian inversion via string diagrams*. The former explicitly distinguishes distribution-carrying objects and support-aware inverses from ordinary arbitrary kernels. [Primary MFCS 2023 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol272-mfcs2023/LIPIcs.MFCS.2023.24/LIPIcs.MFCS.2023.24.pdf).

### Proposition 4.2 — one internal interface cancels probabilistically

For adjacent measured kernels `K:A⇝B`, `L:B⇝C`, and compatible measured maps `f:A'→A`, `g:B'→B`, `h:C'→C`,

\[
 (FKS_g)(GLS_h)=FKLS_h. \tag{4.4}
\]

**Proof.** Insert `S_gG=I_B` between `K` and `L`. QED.

The fine path uses **one shared middle value** `b'`, not two independently drawn copies later identified. Equation (4.4) proves projected distributional agreement. It is not a theorem that `R` is cartesian among all normalized lifts: Theorem 2.1 still allows many different `λ`, whereas a chosen prior picks only one. Nor does it discover the actual fine interface measure: `β'` was supplied as additional data or inferred from a known common law.

### Proposition 4.3 — original witness exactness has the stricter boundary

In the original actual-span restriction, the comparison that forgets a newly inserted middle `b'` has fibre `g^{-1}(b)` over a feasible coarse path with middle value `b`. Consequently this span witness map is bijective exactly when every feasible middle value has exactly one lift. Bayesian weighting does not alter this cardinality condition. For the dynamic graph target the same test must be applied separately to states and actual events, including states with no outgoing events; an event-only calculation is not sufficient for `Graph.IsIso`.

**Proof.** This is the actual coordinate calculation: fixing all coarse path records fixes `b`, and the remaining fine coordinate is exactly any `b'` satisfying `g(b')=b`. A fibre is a singleton precisely under the displayed condition. QED.

**Explicit separation.** Let `A=B=C={*}`, `K=L=(1)`, and `B'={0,1}` with its fair measure. The refined path has two actual middle witnesses, each of weight `1/2`, while the original path has one witness of weight one. Forgetting the bit preserves probability and the external law but is not an event bijection. It is not `Op.Exact` in the unchanged dynamic target. Calling it exact requires changing the equivalence notion, not citing the old theorem.

### Crossing refinements still need a common coupling

For measured surjections `X→B←Y`, the formula

\[
 \rho(x,y)=\mathbf1_{g(x)=h(y)}\frac{\mu_X(x)\mu_Y(y)}{\mu_B(g(x))}
\]

gives a valid conditionally independent coupling on the fibre product. But the actual joint coupling is not fixed by its two marginals. With singleton `B` and two fair bits, both the diagonal coupling and the independent coupling have those marginals. Their actual supports and their joint events differ. Thus this construction is a possible positive assembly, not proof that independently learned local descriptions are the same retained root process. Root-dependent coupling data must be preserved if already available; they must not be replaced silently by independence.

## 5. Reuse through time: exact finite causal condition

The measured construction above is static. A boundary distribution can depend on time, past observations, actions or the world. Picking a separate Bayesian section in each such context does not implement one fixed causal physical table. Even a stationary prior is insufficient.

Let a fine controlled hidden-state process have finite state set `X`, action set `A`, observation set `O`, and nonnegative symbol matrices

\[
 M_{a,o}(x,x')=\Pr(o,x'\mid x,a),\qquad
 \sum_o M_{a,o}{\bf1}={\bf1}.
\]

Fix a surjection `q:X→B`, its matrix `Q`, and a stochastic section `S:B⇝X`, so `SQ=I_B`. A *fixed-section split realization* means that after every observed action/outcome history, the unnormalized fine distribution is the corresponding coarse distribution multiplied by the **same** `S`. The condition is required for every coarse initial distribution, rather than only accidentally on one reachable subspace.

### Theorem 5.1 — exact fixed-section instrument criterion

A fixed-section split realization exists if and only if

\[
 SM_{a,o}=SM_{a,o}QS\qquad\text{for all }a,o. \tag{5.1}
\]

Its coarse instrument is uniquely forced to be

\[
 \overline M_{a,o}=SM_{a,o}Q, \tag{5.2}
\]

is nonnegative and action-normalized, and satisfies

\[
 SM_{a,o}=\overline M_{a,o}S. \tag{5.3}
\]

For any coarse initial law `\bar λ`, set `λ=\bar λS`. Fine and coarse observable transcript laws then agree at every finite horizon under every common causal policy using those same action and observation alphabets.

**Proof.** A one-step posterior-closed realization requires (5.3) row by row. Multiplying it by `Q` and using `SQ=I` gives (5.2), and substitution gives (5.1). Conversely (5.1) and (5.2) give (5.3). Nonnegativity is immediate. Since `Q1=1`, summing over observations gives `Σ_o \bar M_{a,o}1=S1=1`. Repeatedly using (5.3) yields

\[
 \lambda M_{a_1,o_1}\cdots M_{a_T,o_T}
 =\bar\lambda\overline M_{a_1,o_1}\cdots\overline M_{a_T,o_T}S.
\]

Multiplication by `1`, with `S1=1`, gives equality of every prescribed action/outcome word. Multiplying by the common policy's action probabilities on each observation prefix gives equality of each adaptive transcript probability. QED.

This criterion is exact **within the stated split-realization class**, not necessary for all behaviorally equivalent positive realizations. It is a stochastic intertwining/minimization condition, not a new general identification theorem. Given `q,S`, its finite check is direct matrix arithmetic; finding unknown local assignments, separators and causal tables remains a different problem. The comparison line is the established Markov-function/intertwining and weighted-automata simulation literature; a theorem-level historical identity for this particular controlled-instrument formulation was not exhaustively audited.

### Strictly positive noisy counterexample

Take two fine states, no effective control, and

\[
 P=\begin{pmatrix}3/4&1/4\\1/4&3/4\end{pmatrix},\quad
 D_0=\operatorname{diag}(3/4,1/4),\quad D_1=I-D_0,
 \quad M_o=PD_o.
\]

The hidden state flips with probability `1/4`; its posttransition observation flips with probability `1/4`. Every entry of both symbol matrices is strictly positive. Coarsen to the singleton, `Q=(1,1)^T`, `S=(1/2,1/2)`. The stationary transition condition holds:

\[
 SP=S.
\]

But

\[
 SM_0=(3/8,1/8)\ne(1/4,1/4)=(SM_0Q)S.
\]

The coarse one-state instrument would emit independent fair observations. The true stationary model instead satisfies

\[
 \Pr(Y_{t+1}=Y_t)=\tfrac12+\tfrac12(1-2\cdot\tfrac14)(1-2\cdot\tfrac14)^2
 =\tfrac9{16}\ne\tfrac12.
\]

Thus matching one-step marginals and the invariant hidden-state distribution does not preserve the single persistent observed process. This failure involves no exact hidden-state decoder, deterministic observation, zero-probability support trick or revealing reset. A time/history-dependent posterior would repair prediction, but storing and updating that posterior is extra runtime information unless a separate finite causal realization is supplied.

## 6. What follows for unknown typed allocation

Theorems 2–5 are not an allocation algorithm. They make the remaining problem precise enough to reject several invalid shortcuts:

- The learned `p_i` already supplies positivity and coherent stochastic assembly in its own representation. Do not demand a fresh positivity proof as an artificial open problem.
- A declared interface **class** may say which kinds of maps, ports and resource costs are allowed. It may not provide the sought assignment of latent factors, observation mechanisms and shared state to those ports.
- An external physical coupling can appear in a plant kernel without requiring a robot to sense and retransmit its hidden arguments. Robot communication is charged only when the implementation actually routes robot-held information.
- A port used by a controller must be a function/kernel of its permitted causal information. Mathematical access to the learned latent state is not runtime access.
- A learned observation kernel must either be allocated to admissible generating mechanisms or retained as an explicitly charged global mechanism. No inverse noisy observation decoder is assumed.
- Ordinary blockwise coordinate reparameterizations that transport **all** kernels and interface maps are coordinate gauges. They are not separate physical ambiguity. Residual transformations that do not preserve the admissible local implementation class require an explicit action on candidate realizations, not a blanket cost-invariance assertion.
- A stochastic section can be a proof-coordinate coupling, an analyst's posterior, or a physical sampler. These are different roles; only the last allocates physical randomness, timing and storage.

### Required next theorem, not achieved here

For a frozen finite-state learner/access model, give an algorithm or structured constructive procedure taking its identified model/equivalence class and returning **unknown** components, emitted/readout mechanisms and actual admissible ports, with:

1. causal resource-feasible candidate realizations; a later robust deployment claim additionally needs one chosen implementation shared across its covered worlds/contexts, but general discovery may output alternative realizations with different implementations;
2. nonnegative initialization and instruments reproducing the same learned joint process;
3. full actual graph-map witnesses and probability compatibility into the original `Assignment.calculus` (or a proved conservative enrichment);
4. a positive construction on a growing interacting class whose required interfaces are not already supplied or automatic;
5. a sound obstruction/alternative result within precisely that same class;
6. coherent permitted interface changes, with a stated separation between exact event bijections, probability-preserving maps and operational simulations;
7. an honest comparison against structured realization, stochastic minimization and controller-interface results.

Finite deterministic profile quotients and their cardinality bounds repeat existing project machinery unless the new theorem proves an additional structural synthesis gain. Bounded enumeration of candidate partitions and tables is a baseline, not by itself the requested contribution. A continuous finite-port obstruction would not discharge this finite-state target, and finite-message restrictions must be motivated rather than imposed to manufacture failure.

## 7. Baseline map and nonclaims

| Baseline | What it already contributes | What is not supplied by citing it |
|---|---|---|
| Lachapelle et al., CLeaR 2022; arXiv:2401.04890v2 | Joint learned representation, sparse latent mechanisms/graph, positive normalized process, precise residual identifiability | This report's finite-state learner; unknown assignment to a separately restricted physical resource class; arbitrary controlled coverage |
| Lessard–Kristalny–Rantzer, *On Structured Realizability and Stabilizability of Linear Systems* | Demonstrates that structured input/output behavior need not admit the desired structured state-space realization; links controller structure and realization | A new principle merely from renaming sparsity as types; nonlinear hidden stochastic decomposition and actual witness lifting |
| Calbert–Girard–Jungers, *Characterizing simulation relations through control architectures*, v2 | Exact dependence-sensitive control-interface/abstraction relationships | Discovery of unknown components from raw readouts, or free access to latent states in the current problem |
| Bayesian inversion/disintegration (Cho–Jacobs; Braithwaite–Hedges–St Clere Smithe) | Normalized fibre kernels with prior/support data, compositional inversion in the correct typed setting | Naked all-map normalized pullbacks, discovery of the fine prior, universal cartesian uniqueness among all liftings |
| Markov intertwining / probabilistic weighted automata | Positive simulation identities and invariant finite linear representations | A new main result merely from equation (5.3); unknown resource-local synthesis |
| Original dynamic `Calc` and graph-span model | Actual occurrence maps, complete profile typing, retained nullaries, exact event-bijection marking, witnessed fibre calculation | Probabilities, normalization, physical sampler realizability, or general interface-change probability preservation |

Primary comparison sources: [Lachapelle CLeaR 2022](https://proceedings.mlr.press/v177/lachapelle22a.html); [extended v2](https://arxiv.org/abs/2401.04890v2); [Lessard et al.](https://arxiv.org/abs/1212.1839); [Calbert et al. v2](https://arxiv.org/html/2410.06083v2); [MFCS Bayesian inference](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2023.24); [Fritz's synthetic probability framework](https://arxiv.org/abs/1908.07021).

No claim of scientific priority is made for the elementary lift classification, Bayesian composition, stochastic intertwining or the counterexamples. The contribution of this note is to state the exact obstruction to one tempting bridge, identify the original actual-map location of the mismatch, and prevent a static probability repair from being mistaken for a resource-feasible persistent implementation.

## 8. Verification and completion status

`verify_typed_realization_bridge.py` checks the finite examples using exact rational arithmetic: the surjection-coherence contradiction, normalized adjacent cancellation, the noisy temporal counterexample and its two-observation probability. It does not prove the general theorems, synthesize a decomposition, or certify arbitrary learned parameters.

**Completed:** explicit finite lifting theorem/proof; impossibility of coherent naked-surjection sections; measured nested repair/proof; exact witness-fibre mismatch; fixed-section instrument criterion/proof; positive-noise temporal counterexample; original API and baseline map.

**Blocked main target:** a substantive resource-allocation/discovery theorem beyond prior profile/minimization machinery has not been proved. The exact next action is to freeze one finite-state learnable interacting family and independent operational port class, then prove an unknown-allocation construction and obstruction while respecting the distinctions above. Selecting that family cannot itself smuggle in the positive frame, allocation or interface solution.

**Not performed:** uploads, contract edits, acceptance/status changes, continuous-to-finite reduction, finite-data inference, all-profile stochastic equipment closure, or a claim that these supporting results complete O2/O6/O8.
