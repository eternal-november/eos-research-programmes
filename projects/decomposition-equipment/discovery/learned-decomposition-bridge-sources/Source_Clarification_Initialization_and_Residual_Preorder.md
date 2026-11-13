# Initialization and residual preorder source clarification

28 October 2026

## Finding

**The identified joint laws in both sources really include a product initialization.** They do not condition on an arbitrary hidden prehistory. The proposed triangular transport rigidity argument is therefore not blocked by that possible loophole. The source graphical criterion is also genuinely stronger than having singleton strongly connected components of the residual preorder: it excludes all strict comparabilities, not just equal signatures.

This opens a legitimate additional consequence to prove from the existing theorem outputs. It is not evidence of scientific novelty, and it does not turn continuous population identification into finite resource discovery. The independent rigidity worker is checking the actual transport theorem. This note establishes the source facts, the mask derivation, and exact boundary examples.

## 1 Product initialization is part of the identified law

### CLeaR 2022

Primary source: [published PDF](https://proceedings.mlr.press/v177/lachapelle22a/lachapelle22a.pdf).

- **Page 3:** the sequences are (Z^1,\ldots,Z^T) and (A^0,\ldots,A^{T-1}); (Z^{<t}) is the actually indexed earlier latent sequence.
- **Page 4, equation (1):** conditional latent factorization is imposed for the model, with no exemption at (t=1). Thus (Z^{<1}) is empty and the initial conditional law is product given (A^0). The exponential family expression (2) likewise includes that time.
- **Pages 20–21, equations (17)–(28):** equality of the full noisy observation law, at fixed auxiliary sequence, is deconvolved to equality of the full noiseless trajectory laws, using the common Gaussian noise distribution. The learned and true latent trajectory laws are related by the representation diffeomorphism.
- **Page 22, equations (30)–(33):** the joint density is written as a product from (t=1) to (T).
- **Page 22, equations (34)–(36):** integrating suffix variables gives each prefix equality and then each conditional equality. Taking the first prefix gives the initial law equality directly. There is no extra unobserved initial vector being conditioned on.
- **Pages 5–6, Definitions 1–2 and Theorem 4:** the representation relation is one **constant** invertible matrix on the stacked sufficient statistics, plus a constant offset. Theorem 5 further assumes scalar invertible coordinate statistics.
- **Page 42, Appendix A.4.3:** an optional extension permits the first conditional variance related parameter to differ from later ones, while restricting the variability witness points away from the first time. This does not remove initial coordinate independence or remove the initial law from observational equivalence.

The direction of (v) used in the 2022 proof is the inverse of the direction chosen in the 2026 exposition. Use the explicit sufficient statistic relation instead of conflating the two conventions:

\[
s(Z)=L\,s(\hat Z)+b
\]

for appropriately coupled equivalent representations. At a fixed admissible (a^0), both vectors of sufficient statistics have independent coordinates because the original coordinates are independent and (s) is componentwise.

S22 does not explicitly set every coordinate support to all of \(\mathbb R\). That is not necessary for the affine triangular argument: a normalized fixed-base exponential family has context-independent support, and scalar minimality ensures the statistic is not constant on that support. No finite variance or interval support is needed for the elementary “a probability measure cannot have a nonzero translation period” argument. If making this consequence completely formal, state the standard finite-natural-parameter/nondegeneracy facts rather than importing an unjustified covariance assumption.

### Nonparametric v2

Primary sources: [version pinned HTML](https://arxiv.org/html/2401.04890v2), [same version PDF](https://arxiv.org/pdf/2401.04890v2).

- **PDF page 8, Assumption 2; HTML [Assumption 2](https://arxiv.org/html/2401.04890v2#Thmassumption2):** all conditional coordinate densities have support \(\mathbb R\), and the text explicitly sets
  \[
  p(z^1\mid z^{<1},a^{<1})=p(z^1\mid a^0)=\prod_i p(z_i^1\mid a^0).
  \]
- **PDF page 9, §2.1:** the observation density integrates the latent product from (t=1) through (T).
- **PDF page 11, Definition 4; HTML Definition 6:** observational equivalence concerns the complete observation sequence, not only a transition likelihood conditional on an omitted (z^0).
- **PDF page 12, Definition 5, equation (6); HTML Definition 7:** diffeomorphism transport holds for **all** (t\in[T]), hence for initialization.
- **PDF page 13, Proposition 2; HTML Proposition 8:** observational equivalence implies this diffeomorphism equivalence.

Full support and a density imply a continuous, strictly increasing scalar CDF, even if the density vanishes at some points. They do not imply a uniform positive density lower bound. For the scalar quantile argument, a uniform lower bound is unnecessary. For the likelihood-ratio/score extension, ratios must be used where the selected densities are positive; continuity gives the required local identities there. Do not silently promote “full support” to everywhere bounded-away-from-zero density.

## 2 The actual residual mask is a preorder

For combined action and temporal consistency, define the signature of latent index (i) as

\[
\mathcal S_i=(\operatorname{Pa}^a_i,\operatorname{Pa}^z_i,\operatorname{Ch}^z_i).
\]

Define (i\preceq j) precisely when all three component sets for (i) are included in the corresponding sets for (j). This is a reflexive transitive relation. Its strongly connected classes are exactly **equal signature classes**. For action-only consistency use only \(\operatorname{Pa}^a_i\); for temporal-only consistency use the latter two sets.

### S26 direct source

The graph-preserving condition says that dependence (c_i\) on (z_j\) is forbidden whenever row (i) of a preserved graph is not included in row (j). Preserving (G^a,G^z,(G^z)^\top) therefore gives exactly the signature preorder envelope above. This follows from HTML Definitions 15–16 and Proposition 17, together with Definitions 21/31 and the combined relation in §3.6. PDF numbering is Definition 11–12, Proposition 3, Definitions 13–15.

Every admissible residual diffeomorphism and its inverse preserve this preorder envelope. After a topological ordering of its strongly connected classes, the maps are block triangular; blocks can depend on their own coordinates and strictly upper classes. This establishes invariant coordinate upper sets. It does **not** establish that every allowed triangular map transports any particular source product law to another product law.

### S22 derivation from the proof

Theorem 5 does not explicitly name this preorder. Its Appendix A.3.1 **Lemma 19, pages 31–33**, supplies the needed stronger information before invoking the graphical criterion.

Let (N\) be the support of the constant sufficient-statistic mixing matrix (L\), and let (P e_i=e_{\sigma(i)}\) be the matched permutation with (L_{i,\sigma(i)}\ne0\). Equations **(109)** and **(110)** state, respectively,

\[
G^z_{ij}=1\ \Longrightarrow\ N_{i,\cdot}\times N_{j,\cdot}\subseteq\hat G^z,
\qquad
G^a_{i\ell}=1\ \Longrightarrow\ N_{i,\cdot}\times\{\ell\}\subseteq\hat G^a.
\]

The sparsity step makes \(\hat G^z=PG^zP^\top\), \(\hat G^a=PG^a\). Set **\(M=LP\)**, so every diagonal entry of (M\) is nonzero. If (M_{ik}\ne0\), combine it with those diagonal entries:

- (G^z_{ij}=1\) gives (G^z_{kj}=1\), so \(\operatorname{Pa}^z_i\subseteq\operatorname{Pa}^z_k\).
- (G^z_{ji}=1\) gives (G^z_{jk}=1\), so \(\operatorname{Ch}^z_i\subseteq\operatorname{Ch}^z_k\).
- (G^a_{i\ell}=1\) gives (G^a_{k\ell}=1\), so \(\operatorname{Pa}^a_i\subseteq\operatorname{Pa}^a_k\).

Hence (M_{ik}\ne0\) requires (i\preceq k\). This is the same preorder envelope, now for a **constant linear** map on coordinatewise sufficient statistics. The affine offset has no effect on the dependency mask.

## 3 The source graphical criterion is not the singleton class criterion

For each (i\), its upper set is exactly

\[
\uparrow i=
\left(\bigcap_{j\in\operatorname{Ch}^z_i}\operatorname{Pa}^z_j\right)
\cap\left(\bigcap_{j\in\operatorname{Pa}^z_i}\operatorname{Ch}^z_j\right)
\cap\left(\bigcap_{\ell\in\operatorname{Pa}^a_i}\operatorname{Ch}^a_\ell\right).
\]

Thus S26 Assumption 5 (PDF p27) says \(\uparrow i=\{i\}\) for every (i\): **no distinct comparable signatures**. The S22 existential intersection criterion is equivalent: if some family of incidence sets containing (i\) isolates it, then intersecting all such sets also isolates it; conversely the full intersection is an allowed choice.

Having singleton strongly connected classes says only that no two signatures are equal. Strict inclusions may remain. For example, with no actions,

\[
G^z=\begin{pmatrix}1&1&0\\1&1&1\\0&1&1\end{pmatrix},
\]

all three row/column signatures differ, but (1\prec2\) and (3\prec2\). The strongly connected classes are singletons, yet the source graphical criterion fails. This graph comparison alone is not a complete source model; source variability still needs verification for an actual mechanism family.

## 4 What the proposed rigidity would legitimately add

**Scalar nonlinear case.** In the full-support S26 setting, a triangular singleton fibre is a scalar diffeomorphism (c_i(\cdot,u)\). The upper coordinate map is invertible, so independence of target coordinates makes the pushforward distribution of this fibre independent of (u\), at one fixed auxiliary initialization. Source scalar full support gives unique increasing transport, and a continuous nonzero derivative on the connected domain fixes its orientation. The decreasing transport is also unique once that orientation is fixed. Thus the fibre map cannot depend on (u\). This is the correct route to reducing a singleton residual class to an autonomous coordinate transformation; no hidden coordinate readout is being assumed.

**Affine S22 case.** A block triangular constant affine map between independent initial coordinate vectors can have no strict off-diagonal block. Conditioning on the invertibly transformed upper tail makes each lower block's law a translate of a fixed law. Independence requires these translates to agree. A probability measure has no nonzero translation period, so the upper shift is almost surely constant; nondegenerate independent scalar inputs force all its coefficients to vanish. No moment argument is necessary. Therefore constant affine residual maps can mix only within equal-signature classes. This is stronger than the source's stated graphical sufficient condition when signatures are distinct but comparable. It is an additional deduction from source output, not a claim the source theorem is false or that the deduction is novel.

**Score-family refinement.** For a nonempty common auxiliary parent signature of a residual block (B\), choose an auxiliary coordinate \(\ell\) present in that signature. Then (B\subseteq\operatorname{Ch}^a_\ell\). Projecting S26 Assumption 7's score-difference span onto (B\) gives a full \(\mathbb R^B\) span of block log-likelihood-ratio gradients. The projected functions depend on current (z_B\), not other current coordinates; Fubini therefore transfers the almost-everywhere full-space statement to almost every (z_B\). Assumption 6 gives the analogous claim by limits of finite action differences, using regular-closed action support and continuity at its boundary. This appears to support the rigidity worker's proposed elimination of base-dependent continuous symmetries for action-influenced blocks.

Use the correct orientation: if (c_u\) transports learned block law \(\mu_h\) to true block law \(\nu_{v(h)}\), the relative symmetry acting on the **true** family is (c_u\circ c_{u_0}^{-1}\), not (c_{u_0}^{-1}\circ c_u\). Source influence assumptions concern the true family. The independent proof must handle density-zero loci and context quantifiers explicitly before promoting this observation to a theorem.

## 5 Exact counterexamples that bound the proposed improvement

### Arbitrary graph-preserving maps are not an admissible orbit

Let two independent standard Gaussian scalar inputs have nested allowed signatures. The triangular shear (c(x_1,x_2)=(x_1+x_2,x_2)\) respects that envelope, but its outputs are correlated. Thus the graph-preserving envelope is necessary support information, not permission to ignore product conditional laws. This is exactly why initialization can tighten the envelope.

### Genuine nonlinear base dependence survives in an uninfluenced multidimensional block

Take (T=1\), (m=3\), one continuous auxiliary (a\), and

\[
U=(Z_1,Z_2)\sim\mathcal N(0,I_2),\quad
V=Z_3\sim\mathcal N(a,1),\quad U\perp V.
\]

Set (G^a=(0,0,1)^\top\), (G^z=0\), (f=\mathrm{id}\), and use any known Gaussian measurement noise variance. For a smooth nonconstant \(\phi:\mathbb R\to\mathbb R\), set

\[
c(u,v)=(R_{\phi(v)}u,v),
\]

where (R_\alpha\) is a two-dimensional rotation. This is a smooth diffeomorphism with inverse \((u,v)\mapsto(R_{-\phi(v)}u,v)\). It preserves the conditional product law for **every** (a\), because the isotropic Gaussian block is rotation invariant conditional on (V=v\). Take \(\hat p=p\), \(\hat f=c\): the observation laws coincide exactly.

All S26 A1–A4 hold. For Theorem 22, the action mixed-derivative column is \((0,0,1)^\top\), satisfying Assumption 6 on the sole affected coordinate. The discrete version with admissible actions (a=0,1\) satisfies Assumption 7 as well. Sparsity is unchanged. The unacted class \(\{1,2\}\) genuinely depends on the acted scalar base \(\{3\}\). Therefore a blanket claim that **all S26 residual maps become block diagonal** is false. This does not refute singleton rigidity or action-influenced-block rigidity.

This example does not meet S22's full natural-parameter variability: the unacted means are constant. It must not be used to refute the S22 affine conclusion.

### Within-class ambiguity can remain even for S22

For (T=1\), one scalar action and two latent coordinates, take

\[
Z\mid a\sim\mathcal N((a,a^2),I_2),\qquad G^a=(1,1)^\top,\quad G^z=0.
\]

The scalar sufficient statistic is identity; the natural-parameter curve has full affine span; action finite differences span \(\mathbb R^2\). Any nontrivial fixed orthogonal rotation transports this conditional family to another coordinate-independent Gaussian family with the same two-edge action mask, after changing the decoder accordingly. Both coordinates have the same signature. Thus reduction to equal-signature blocks does not in general imply finer coordinate identification.

## Scope conclusion

There is no initial-law loophole in the stated population comparison. The residual envelope is a preorder, and the source graphical criterion is an antichain condition, strictly stronger than distinct signatures. Initial product structure supplies legitimate extra leverage. The scalar and affine routes should be proved and reviewed as additional deductions; the nonlinear multidimensional route requires a symmetry/score argument and cannot hold for all blocks, as the explicit source-valid rotation example shows. None of these statements supplies runtime state access, finite sample confidence, bounded messages, or an unqualified novelty claim.

## 6 A growing source-valid separation test

For every (m\ge2\), take (T=1\), (m\) auxiliary coordinates, and

\[
Z\mid a\sim\mathcal N(\mu(a),I_m),\qquad
\mu_i(a)=\sum_{\ell=1}^{i}a_\ell^{i-\ell+1}.
\]

Use (\mathcal A=\mathbb R^m\) for the continuous theorem, or (\mathcal A=\{0,1,\ldots,m\}^m\) for the discrete theorem. The latent action parent signatures are \(\{1,\ldots,i\}\); there are no temporal edges. The decoder can be any unknown source-admissible diffeomorphism, with the known independent Gaussian measurement noise.

This is a mechanism family, not merely a graph with identifiability assumed:

- With the identity scalar sufficient statistics, \(\mu(0)=0\) and \(\mu(e_j)\) is the vector of zeros before (j\) and ones from (j\) onward. These (m\) vectors form an invertible triangular matrix, proving S22 full natural-parameter variability.
- For action \(\ell\), its affected coordinates are (i=\ell,\ldots,m\). The continuous derivative components are \((i-\ell+1)a_\ell^{i-\ell}\), a basis of polynomials with distinct degrees (0,\ldots,m-\ell\). Evaluating at sufficiently many distinct auxiliary values spans the affected coordinate subspace, as required by S26 Assumption 6.
- For discrete changes of size one at base actions (r e_\ell\), (r=0,\ldots,m-\ell\), the affected components are \((r+1)^k-r^k\), (k=1,\ldots,m-\ell+1\). These polynomials have distinct degrees and nonzero leading coefficients. Their evaluation matrix is invertible by the Vandermonde argument. All base and changed actions lie in the displayed finite alphabet. This proves S22 action variability and S26 Assumption 7.
- Temporal variability is vacuous for the empty temporal graph. Both models still need exact observation matching and the corresponding sparsity bound; this is not an optimization guarantee.

All signatures differ, so the residual strongly connected classes are singletons, but every signature except the largest is strictly included in another. The published graphical sufficient criterion therefore fails. The proposed scalar/affine rigidity consequence would nevertheless give complete disentanglement. This is an appropriate growing regression to distinguish that deduction from simply restating the published graphical criterion. It is an action-driven conditional model, **not** by itself the required growing persistently interacting finite-resource O2 family.

## 7 Finite state and disconnected support boundary

The scalar nonlinear deduction cannot be transferred to finite state components merely by quantizing the source coordinates. If (X,Y\) are independent fair bits, the triangular bijection

\[
(X,Y)\longmapsto(X\mathbin{\mathrm{xor}}Y,Y)
\]

preserves their independent product law and genuinely depends on the upper coordinate. The continuous source's connected full real support and monotone scalar diffeomorphisms are doing substantive work. Similarly, disconnected continuous base supports can permit an increasing fibre on one connected component and a decreasing fibre on another while preserving a symmetric scalar law. S26's full \(\mathbb R^m\) support excludes that escape. S22's constant real affine argument is separate and does not identify addition modulo two with real translation.
