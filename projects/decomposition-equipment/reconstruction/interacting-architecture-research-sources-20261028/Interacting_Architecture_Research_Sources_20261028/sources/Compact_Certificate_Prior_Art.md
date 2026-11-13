# Prior-art audit: control-derived compact stochastic certificates

**2026-10-28 UTC. Scope:** the restricted candidate theorem: product hidden state; invertible idle drift \(D\); one-local-actuator-at-a-time transitions \(DK_{i,k}\); full local equal-column-sum linear spans; a signed CP representation of the hidden-to-predictive intertwiner; sparse observationally equivalent initialization; one-step tensor-network verification.

**Verdict:** all main ingredients have strong classical baselines. In particular, the downward-closed constant/contrast submodule lemma is a direct specialization of structural matrix algebra theory, not just an analogy to it. I have not found the exact integrated stochastic certificate and resource statement in one source. That absence does **not** establish novelty. Safe positioning is a restricted certificate-completeness theorem assembled from known methods, whose utility requires nonvacuous compressed examples and careful complexity accounting.

## 1. Closest primary-source baselines

| Ingredient | Primary source and relation |
|---|---|
| One-step intertwiner implies all-word equivalence | [Ésik and Maletti, *Simulation vs. Equivalence* (2010)](https://arxiv.org/abs/1004.2426) treats matrix simulations as finite witnesses of weighted-automata equivalence. The proposed equations \(F\pi=\alpha,\ FH_a=A_aF,\ \ell F=\mathbf1^T\) are exactly this kind of simulation, in column convention. See also the explicit three-equation definition in Appendix A.2 of [Winter, *A Completeness Result for Finite λ-bisimulations* (2015)](https://www.mimuw.edu.pl/~jwinter/articles/fossacs15.pdf). |
| Finite linear-span equivalence algorithm | [Tzeng, *A Polynomial-Time Algorithm for the Equivalence of Probabilistic Automata* (1992)](https://doi.org/10.1137/0221017) gives polynomial-time equivalence testing in explicit state dimensions. Replacing exponential hidden-state expansion with compact structured witnesses is a resource refinement, not a new equivalence principle. |
| Controlled observable rank and predictive quotient | [Singh, James and Rudary, *Predictive State Representations: A New Theory for Modeling Dynamical Systems* (UAI 2004), especially Theorem 6](https://faculty.cc.gatech.edu/~isbell/reading/papers/uai2004psr.pdf) identifies finite linear PSR dimension with system-dynamics-matrix rank for controlled processes. The interpretation of initialized controlled Hankel rank as minimal linear predictive dimension is established. |
| Downset invariant-subspace classification | [Akkurt, Barker and Wild, *Structural matrix algebras and their lattices of invariant subspaces*, LAA 394 (2005), 25–38, Theorems 1–4](https://doi.org/10.1016/j.laa.2004.05.009) relates coordinate-pattern algebras indexed by preorders to distributive lattices of coordinate subspaces. Theorems 1–2 provide the shared-basis/coordinate-lattice mechanism. The paper explicitly identifies these as already-known results reproven there; this is not an earliest-priority attribution. The exact application is worked out below. |
| Stochastic/affine algebra baseline | [Johnson, *Markov-type Lie groups in GL(n,R)* (1985)](https://sc.edu/study/colleges_schools/artsandsciences/physics_and_astronomy/research/asg/documents/markov_type_lie_groups_in_glnr-1985.pdf) identifies the signed, invertible column-sum-one group with an affine group in one lower dimension. Thus the constant-plus-contrast triangular/affine structure is itself longstanding. |
| Initial-law compression to at most \(r\) points | [Piazzon, Sommariva and Vianello, *Caratheodory–Tchakaloff Subsampling* (2017), Theorem 1.1](https://drna.padovauniversitypress.it/system/files/papers/PiazzonSommarivaVianello_2017_CTS.pdf) states precisely the finite-support result: moments of an \(r\)-dimensional function space can be preserved by positive weights on at most \(r\) original support points. Apply it to predictive features, including the constant function. No control hypothesis is needed for this step. |
| Factored model reduction without explicit global enumeration | [Dean and Givan, *Model Minimization in Markov Decision Processes* (AAAI 1997)](https://aiinternational.org/Library/AAAI/1997/aaai97-017.php), and [Givan, Dean and Greig, *Equivalence notions and model minimization in Markov decision processes* (2003)](https://doi.org/10.1016/S0004-3702(02)00376-4), explicitly compute factored state abstractions without enumerating the full state space. Their partition/bisimulation quotient is more restrictive than a signed linear predictive quotient: this is adjacent prior art, not an assertion that the proposed quotient is identical. |
| Width-controlled tensor contraction | [Markov and Shi, *Simulating Quantum Computation by Contracting Tensor Networks* (2008)](https://arxiv.org/abs/quant-ph/0511069) establishes polynomial-size times exponential-width contraction bounds. Its contraction machinery applies to general finite tensor entries; quantum terminology does not create a new operation when used for real stochastic tensors. |
| Automata–tensor-network connection | [Srinivasan et al., *Quantum Tensor Networks, Stochastic Processes, and Weighted Automata* (2021)](https://arxiv.org/abs/2010.10653) establishes explicit model correspondences among these literatures. [Li, Precup and Rabusseau, *Connecting Weighted Automata, Tensor Networks and Recurrent Neural Networks through Spectral Learning*](https://arxiv.org/abs/2010.10029) also develops the WFA/tensor-train connection. Merely combining predictive models with tensor representations is not new. |

## 2. Exact identification of the module lemma

Let \(V_i^*=\operatorname{span}\{\mathbf1_i^T\}\oplus U_i\), where \(U_i\) is any chosen contrast complement. In these **row-function coordinates**, the algebra
\[
\mathcal S_i=\{K:\mathbf1_i^TK=\lambda\mathbf1_i^T\}
\]
becomes
\[
\left\{\begin{pmatrix}\lambda&0\\u&M\end{pmatrix}:
\lambda\in\mathbb R,\ u\in\mathbb R^{d_i-1},\
M\in M_{d_i-1}(\mathbb R)\right\}.
\]
Thus constants remain constants, while a contrast can map arbitrarily into contrasts and constants.

In the product basis, the generated algebra \(\bigotimes_i\mathcal S_i\) is a **structural matrix algebra**. Its diagonal blocks are
\[
W_S=\bigotimes_{i\in S}U_i\otimes
\bigotimes_{i\notin S}\operatorname{span}\{\mathbf1_i^T\},
\]
and its allowed row-action blocks \(W_S\to W_T\) are exactly all linear maps with \(T\subseteq S\). This follows directly by tensoring local matrix units. Consequently invariant row subspaces are precisely
\[
W=\bigoplus_{S\in\mathcal I}W_S,\qquad
\mathcal I\text{ downward closed}.
\]
Equivalently: product-basis diagonal idempotents isolate coordinates; full within-block matrix units force inclusion of an entire \(W_S\); downward matrix units force inclusion of every lower block. This is the coordinate-order-ideal specialization of the structural-algebra baseline above.

Once \(\dim W=r\), choose \(r\) product functions \(\psi_j\) spanning it. Any intertwiner with this rowspace has
\[
F=\sum_{j=1}^{r}c_j\otimes\psi_j,
\]
where each \(\psi_j\) factors across hidden coordinates. Hence signed CP rank at most \(r\) follows immediately. It is a useful derived bound, but its derivation is a short application of established algebra rather than a new general tensor-rank phenomenon.

## 3. Other short deductions, and their limits

* **Drift cancellation is algebraic.** The unital finite-dimensional transition algebra contains \(D^{-1}\), because Cayley–Hamilton expresses it as a polynomial in invertible \(D\). It therefore contains \(K_{i,k}=D^{-1}(DK_{i,k})\). Full local spans then contain point-reset maps; their products send any normalized initial law to any product point configuration. This proves full *linear* reachable span. It does not say physical positive controls implement a reset.
* **Reachability removes initial-state dependence of rank.** With full reachable span, initialized Hankel rank equals the dimension of the predictive rowspace. The exceptional work is establishing full reachability; the rank equality thereafter is ordinary realization theory.
* **Sparse initialization is only observational replacement.** The at-most-\(r\)-point law need not equal the original correlated law and need not be physically preparable by the allowed actuators. It preserves all predictions because it preserves a basis of \(W\).
* **The signed quotient is not a stochastic state aggregation.** CP terms and observable coordinates may be signed. Neither a nonnegative CP factorization nor a physical decomposition into \(r\) hidden modes follows.
* **Generic full dimension is a serious limitation.** If one predictive row has any nonzero component in the top contrast block \(W_{\{1,\ldots,m\}}\), full local-algebra invariance forces every contrast block and therefore \(r=\prod_i d_i\). Generic unconstrained observation rows have this property. Compression requires protected missing interactions, not merely local controls or an interacting drift.

## 4. What the integrated resource claim must add

The potentially useful statement is: **every observationally compatible candidate within a precisely specified restricted architecture class possesses a bounded-size signed-CP simulation certificate, verifiable without materializing its hidden state space.** To make that meaningful:

1. Charge for the proposed hidden wiring, local tables, CP factors, observable operators, initializer and arithmetic encodings. Existence of small CP rank does not supply its decomposition efficiently.
2. Supply/check a contraction schedule for the **actual doubled residual network**, including observable-operator tensors, copy/equality tensors and all output legs. Do not substitute a width of the original drift graph without proving a bound.
3. Verify each finite one-step identity exactly (or with explicit certified error bounds). A small floating-point residual is not an exact equivalence certificate. Rational/algebraic bit complexity must be distinguished from unit-cost arithmetic.
4. Avoid silently enumerating an exponentially large joint output alphabet or initial support. If outputs are factored, their representation and contraction cost belong in the theorem.
5. Keep verification distinct from discovery, identifiability, minimal architectural size and efficient certificate search. A valid intertwiner proves behavior of a proposed realization, not uniqueness of its latent factors or wiring.
6. Exhibit an interacting family with \(r\ll\prod_i d_i\), and compare against factored bisimulation/linear realization baselines. Otherwise “compact” can be vacuous under the same strong control assumptions.

**Recommendation:** cite the structural-matrix-algebra specialization explicitly; retain the complete proof because it makes assumptions auditable. Describe the outcome as a restricted proof-carrying verification result or benchmark until a concrete nontrivial improvement over these baselines is established. No claim of priority is supported by this audit.

## 5. Quadratic-parity decoder benchmark: direct prior baselines

The proposed reversible-clock example should be positioned as a **witness-language benchmark**, not a new generic circuit-versus-tensor separation. For \(q_G(x)=\bigoplus_{ij\in E(G)}x_ix_j\), its sign tensor \(s_G(x)=(-1)^{q_G(x)}\) is the unnormalized graph-state amplitude tensor. [Hein, Eisert and Briegel, *Multi-party entanglement in graph states* (2004), Proposition 3, Eq. (43)](https://arxiv.org/pdf/quant-ph/0307130) give
\[
\operatorname{rank}_{\mathbb R}(s_G)_{A|B}=2^{\operatorname{rank}_{\mathbb F_2}\Gamma_{A,B}}.
\]
For the **Boolean-valued** decoder tensor, the safe consequence is \(\operatorname{rank}_{\mathbb R}(q_G)_{A|B}\ge 2^{\operatorname{rank}_{\mathbb F_2}\Gamma_{A,B}}-1\), since \(s_G=\mathbf1-2q_G\); do not silently assert the same exact rank formula. Every balanced cut having linear cut-rank therefore forces exponential CP rank and at least one exponential TT bond in every component ordering. TT ranks are precisely the corresponding unfolding ranks: [Oseledets, *Tensor-Train Decomposition* (2011), §2, Theorem 2.1](https://users.math.msu.edu/users/iwenmark/Teaching/CMSE890/TENSOR_oseledets2011.pdf). The stronger connection between graph cut-rank and optimal **tree** tensor-network descriptions is explicit in [Van den Nest, Dür, Vidal and Briegel (2007), Eq. (7), Theorem 3 and §III.C](https://arxiv.org/pdf/quant-ph/0608060). Suitable graphs are not a new existence ingredient: the proof of Proposition 3.3 in [Lee, Lee and Oum, *Rank-width of random graphs* (2012)](https://mathsci.kaist.ac.kr/~sangil/pdf/2010random.pdf) bounds all disjoint \(\lceil n/3\rceil\)-by-\(\lceil n/2\rceil\) adjacency submatrix ranks simultaneously, implying the required balanced-cut property with high probability for constant edge probability. This is an existence statement, not an explicit efficiently certified graph construction.

Polynomial reversible compute/copy/uncompute is classical: [Bennett, *Logical Reversibility of Computation* (1973)](https://www.cs.princeton.edu/courses/archive/fall04/cos576/papers/bennett73.html). Here accumulating edge products into one target bit, routing by adjacent swaps, and reversing the gate list give an elementary polynomial path-circuit construction and cancellation proof. The specific additional benchmark claim to prove is its embedding into the stated stochastic system with predictor rank \(L+1\), together with a forced all-state quotient row whose fixed-phase/ancilla restriction is \(q_G\). Such slicing and output-row contraction cannot increase CP rank or TT bonds, so the obstruction survives basis changes in predictor coordinates. The comparison is between an explicit CP/TT decoder and a circuit decoder **with its supplied cancellation witness**; it is not a lower bound for unrestricted tensor networks, circuit equivalence checking, or discovery. Constant static path-plus-clock width must not be confused with the width of the unfolded computation or doubled residual network. These sources establish the lower-bound and reversible-computation mechanisms; this audit does not establish priority for the exact stochastic packaging.

