# Residual transport rigidity for the learned decomposition bridge

This note checks which triangular dependences in a learned representation's graph-preserving support envelope can actually occur between observationally equivalent product-mechanism models. It supplies proofs for use in the learned-interface bridge, not a separate physical decomposition theorem.

## Conclusions

1. **Singleton SCCs are rigid.** A globally invertible, continuously varying scalar fibre map cannot depend on its connected base if it transports the same full-support scalar law to the same target law at every base. One actually transported product initialization already suffices. Strict positivity of a density is unnecessary.
2. **Higher-dimensional dependence is exactly common symmetry.** Relative to a reference fibre transport, the remaining base-dependent maps must preserve every relevant source block mechanism law. This is a necessary-and-sufficient statement for the specified product-law transports, not for an entire dynamic model with unverified histories or masks.
3. **Dense local likelihood-ratio rank is enough.** The common symmetry group's connected identity component is trivial if finite collections of locally defined likelihood ratios have full-rank gradients on a dense set. Densities may vanish elsewhere. Disconnected symmetries can remain.
4. **The S26 influence assumptions supply such rank for acted-on blocks.** In the source's actual residual preorder, Assumption 6 or 7 removes strict-base dependence into any SCC with a nonempty auxiliary-parent set; Assumption 8 does so for any SCC with a nonempty temporal-parent set. Use the inverse residual map so the symmetry group acts on the true mechanism laws. Parentless multidimensional SCCs need not be rigid.
5. **Affine transport is stronger.** An invertible block-triangular affine map that sends independent, affinely nondegenerate blocks to independent blocks is block diagonal. No moments, densities, connected supports, or non-Gaussianity are required. This applies to S22's scalar invertible sufficient-statistic setting after its matched-permutation residual-support argument.

The scalar mechanism is established monotone/Knothe–Rosenblatt transport rigidity, including explicit causal-representation antecedents in Brehmer et al. (2022), supplementary Lemma 2, CauCA (2023), proof of Theorem 4.2(ii), and Xi–Bloem-Reddy (2023), Proposition 5.2; exact primary credits appear in §4. The affine result uses elementary translation rigidity rather than a new ICA theorem. The contribution claimed here is a carefully delimited source-specific sharpening of what consistency support permits, not scientific priority. See `Rigidity_Prior_Art_Comparison.md`.

## 1 Mathematical setting and fibre maps

Let a finite preorder on coordinate indices have strongly connected classes, called blocks. Its quotient is a finite poset. For block B, let U(B) be its strict upper blocks, with the convention that the B-output may depend on B and U(B). Write E_B = R^{d_B} and E = product_B E_B.

Assume v:E→E is a C1 diffeomorphism and both v and v^{-1} respect this preorder:

\[
 v_B(x)=T_B(x_B,x_{U(B)}).
\]

Every upper-closed block set U has induced maps v_U and (v^{-1})_U. Projecting the two composition identities proves that these are mutual inverses. In particular v_{U(B)} is a diffeomorphism. For each fixed u, the map T_{B,u}:x_B↦T_B(x_B,u) is a diffeomorphism, with inverse

\[
 y_B\longmapsto (v^{-1})_B(y_B,v_{U(B)}(u)).
\]

Thus global triangular invertibility is doing real work: a possibly nonsurjective local fibre is not enough. Joint C1 regularity and nonsingularity of the fibre derivative also follow from this inverse formula. A total order extending the quotient poset gives the usual block-triangular representation.

Nothing below identifies these strict upper coordinates with physical communication ports. They are initially just coordinates in a representation change.

## 2 Product transport determines every fibre transport

### Theorem 1

Let μ = product_B μ_B and ν = product_B ν_B be Borel probability measures on E. Suppose each μ_B has full support and v_*μ=ν. Then

\[
 (T_{B,u})_*\mu_B=\nu_B\qquad\text{for every block B and every base u}. \tag{1}
\]

Conversely, a block-triangular diffeomorphism satisfying (1) transports μ to ν.

**Proof of necessity.** Let X have law μ and Y=v(X). Since v_U is a measurable bijection for U=U(B), σ(Y_U)=σ(X_U). Independence in the source and target gives

\[
 \mathcal L(Y_B\mid X_U=u)
   =(T_{B,u})_*\mu_B
   =\nu_B
\]

for μ_U-almost every u. For each bounded continuous test function f, the function

\[
 u\longmapsto\int f(T_{B,u}(x))\,d\mu_B(x)
\]

is continuous by dominated convergence. A continuous function equal to a constant almost everywhere under a full-support measure equals it everywhere. Applying this to a measure-determining class of bounded continuous functions proves (1) at every u. No moment or density assumption is used.

**Proof of sufficiency.** Order blocks with upper blocks first. Before processing B, the previous transformed blocks determine the previous source blocks by the invertible triangular restriction. X_B is independent of all these source blocks, and its fibre image has law ν_B for every value of its base. Therefore Y_B has conditional law ν_B independent of all previous transformed blocks. Induction gives the target product law. ∎

Only source-base full support is needed for the a.e.-to-everywhere upgrade. Full source-fibre support will matter for scalar uniqueness. Strictly positive densities are a convenient stronger assumption, not a necessary one. If product transport is only asserted at one fixed auxiliary value a0, all statements above concern that conditional law; one must not marginalize a0 and then assume independence still holds.

## 3 The exact common symmetry criterion

Let C be any set of contexts. A context may include time, all past latent states, and admissible auxiliary history. Suppose the same v transports

\[
 \mu^c=\prod_B\mu_B^c
 \quad\text{to}\quad
 \nu^c=\prod_B\nu_B^c
 \qquad(c\in C), \tag{2}
\]

where every source factor has full support. Target ν^c may be indexed by a prescribed transformed history Φ(c), provided it is fixed once c is fixed and does not depend on the **current** base u.

Fix B and a reference base u0. Set T0=T_{B,u0} and

\[
 R_u=T_0^{-1}\circ T_{B,u}.
\]

Theorem 1 gives the exact characterization

\[
 (T_{B,u})_*\mu_B^c=\nu_B^c\ \forall u,c
 \quad\Longleftrightarrow\quad
 T_{B,u}=T_0\circ R_u,
 \quad R_u\in\operatorname{Aut}(\{\mu_B^c\}_{c\in C}), \tag{3}
\]

where T0 transports each source factor to its corresponding target factor and

\[
 \operatorname{Aut}(\{\mu_B^c\}_c)
 =\bigcap_c\{R\in\operatorname{Diff}^{1}(E_B):R_*\mu_B^c=\mu_B^c\}.
\]

The forward direction follows by composing transports; the reverse direction follows by composition and Theorem 1. Also R_{u0}=id. If the base is connected and u↦R_u is continuous in the usual function-space topology, its image lies in the connected identity component of this group. For the given jointly C1 family, evaluation (u,x)↦R_u(x) is continuous, which suffices for all arguments below.

This characterization concerns a **specified collection of actual product laws**. To construct an observationally equivalent dynamic model, one must additionally check every initialization and conditional kernel, the transformed histories, emission maps, and required parent masks. A support-allowed transformation or a symmetry of just one marginal does not settle those obligations. If the conditional source or target factor itself depends on current u, (3) does not apply in this form.

## 4 Scalar rigidity and its exact assumptions

### Theorem 2

If d_B=1 and the base is connected, then T_{B,u}=T0 for every u. In particular, if all SCCs are singleton, v is componentwise in the aligned coordinate labels even when the quotient order has strict comparisons.

**Proof.** The derivative ∂_xT_{B,u}(x) never vanishes. Its sign is constant on the connected product R×E_{U(B)}. Hence T_{B,u} and T0 have the same orientation, and R_u=T0^{-1}T_{B,u} is increasing. It preserves μ_B by (3), using only one transported product law.

The distribution function F(x)=μ_B((−∞,x]) is strictly increasing because μ_B has full support. For an increasing bijection R preserving μ_B,

\[
 F(R(x))=\mu_B(({-\infty},R(x)])
        =\mu_B(R(({-\infty},x]))=F(x).
\]

Strict increase implies R(x)=x for every x. This proof even allows atoms. With atomless positive-density laws, the equivalent transport description is the unique increasing quantile map, or the unique decreasing quantile map when the common orientation is negative. ∎

This is the ordinary scalar monotone transport argument. In the all-singleton case, one can alternatively flip constant target-coordinate signs and invoke uniqueness of the increasing triangular Knothe–Rosenblatt map; the product of marginal quantile maps is itself such a transport. See Spantini, Bigoni and Marzouk, *Inference via Low-Dimensional Couplings*, §3, pp. 4–5 ([primary JMLR paper](https://www.jmlr.org/papers/volume19/17-747/17-747.pdf)); Baptista, Morrison, Zahm and Marzouk give the same transport framework in §3.1 ([primary JMLR paper](https://www.jmlr.org/papers/volume25/21-0022/21-0022.pdf)).

The scalar fibre argument has explicit causal-representation-learning antecedents: **Brehmer–de Haan–Lippe–Cohen (2022), supplementary Lemma 2**, proves constancy of a differentiable family of scalar transports ([published supplement, §A.2](https://papers.nips.cc/paper_files/paper/2022/file/fa567e2b2c870f8f09a87b6e73370869-Supplemental-Conference.pdf)); **Liang et al. (2023), Causal Component Analysis, proof of Theorem 4.2(ii)**, uses that lemma with triangular marginal transport to remove off-diagonal dependence ([published paper, pp. 19–21](https://proceedings.neurips.cc/paper_files/paper/2023/file/67089958e98b243d5cc1881ad60418b8-Paper-Conference.pdf)). **Xi–Bloem-Reddy (2023), Proposition 5.2 and Appendix E.1**, gives the triangular nonlinear-ICA componentwise-identification corollary for full-support independent latent distributions ([primary text](https://arxiv.org/html/2206.00801v5#S5.SS1)). Here the triangular restriction is on the source consistency **residual map**, rather than on the emission maps; fixed orientation flips reduce it to their monotone triangular product-transport argument. The direct proof above retains explicit global invertibility, connected-base and full-support hypotheses and permits atoms. The distinct-signature consequence is a source-specific combination with these established rigidity arguments, not a new scalar transport theorem or an established priority claim. See `Rigidity_Prior_Art_Comparison.md` for the exact comparison and search limits.

### What fails when hypotheses are removed

- **No full-support base:** take X Gaussian, U uniform on [−1,1], independent, and v(x,u)=(x+h(u),u), where smooth h vanishes on [−1,1] but not everywhere. The observed product law is unchanged, but the global map has base dependence outside the support.
- **Disconnected base:** on R×((−∞,0)∪(0,∞)), let v(x,u)=(sign(u)x,u), with a symmetric scalar source law. It is smooth on that disconnected domain, preserves a product law, and has different orientations on the two base components.
- **Different fibre topology:** for a circle-valued uniform X, v(x,u)=(x+φ(u) mod 2π,u) preserves a product law and varies smoothly with u. A circle is not the real-line fibre of Theorem 2.
- **Only a support envelope:** for independent standard Gaussians X,U, the permitted real-line shear (X+U,U) has covariance 1 between outputs and is not a product-law equivalence.

Connectedness is not an optional cosmetic assumption in the monotone-orientation argument. In the actual R^d setup it is automatic for every base.

## 5 Likelihood ratio rigidity with densities that can vanish

Assume now each block mechanism μ_B^c has a C1 density p_c≥0 on R^m, m=d_B. Pointwise strict positivity is not required.

Define the regular-ratio set D to consist of points x for which there are contexts c0,c1,…,cm with all p_cj(x)>0 and

\[
 \det\left[
 \nabla\log\frac{p_{c_1}}{p_{c_0}}(x),\ldots,
 \nabla\log\frac{p_{c_m}}{p_{c_0}}(x)
 \right]\ne0. \tag{4}
\]

These ratios are defined on a common open positive neighborhood of x. Equivalently, the gradients of all available local log-likelihood ratios span R^m. A finite witness always suffices. D is open; the requirement below is that D is dense. An almost-everywhere rank hypothesis implies this.

### Theorem 3

If D is dense, every connected continuous family R_u in the common stabilizer with R_{u0}=id is identically the identity. In particular all base dependence disappears. In the C1 compact-open topology, the stabilizer has trivial connected identity component.

**Proof.** If a C1 diffeomorphism R preserves μ_B^c, change of variables gives

\[
 p_c(R(x))|\det DR(x)|=p_c(x) \tag{5}
\]

Lebesgue-a.e. Both sides are continuous, so (5) holds at every x. Thus each context's positivity set is invariant under R. Dividing (5) for any two positive contexts cancels the Jacobian:

\[
 \log\frac{p_c}{p_{c_0}}(R(x))
 =\log\frac{p_c}{p_{c_0}}(x). \tag{6}
\]

Fix x∈D and its finite witnesses. By the inverse function theorem, x is an isolated point of the common level set of these m log ratios, within their common positivity domain. Equation (6) puts the entire connected orbit {R_u(x):u in the base} into that level set. This orbit contains x. An isolated singleton is open and closed in that level set, so a connected subset containing x contains nothing else. Hence R_u(x)=x for every u. Density of D and continuity in x extend this equality to every x.

The same argument applies to the connected identity component of the stabilizer: evaluation at x is continuous, so its orbit is connected. Its elements fix the dense set D and therefore the whole space. ∎

### The differential version and its limits

For a differentiable base path, define its Eulerian velocity W_u(y)=∂_uR_u(R_u^{-1}(y)). Differentiating (6) gives

\[
 W_u(y)\cdot\nabla\log(p_c/p_{c_0})(y)=0.
\]

Full rank at regular points kills W there, and continuity kills it everywhere when regular points are dense. This is a useful local score proof. The preceding connected-orbit proof is stronger: it needs no derivative with respect to the base and establishes the connected-component claim directly, rather than silently equating zero infinitesimal generators with all possible topological components.

Rank of **raw scores** ∇log p_c is not the condition: their common density-Jacobian term must first be canceled. Nor does full ratio rank prove that the entire stabilizer is trivial. If the global likelihood-ratio features separate points, then (6) does force every symmetry to be identity; that is a stronger, global condition.

### Disconnected symmetries can remain

Let p0 be the standard Gaussian density on R^m and let pi change only coordinate i's variance to a different positive value. The ratios determine x_i². Their gradients have full rank wherever all coordinates are nonzero, a dense set. Nevertheless every fixed coordinate sign flip preserves all these laws. In fact these are the entire C1 stabilizer: R_i(x)²=x_i² forces a fixed sign on each connected half-space, and derivative continuity across x_i=0 makes the two signs agree. Thus the stabilizer is the finite group of 2^m sign choices. A connected base cannot move among them, but the fixed block transport is not absolutely identified.

### Full rank is sufficient but not necessary

On R², take μ0=N(0,I) and μ1=N((1,0),I). The only log ratio, up to constants and scaling, is x1, so rank is one rather than two. A common symmetry fixes x1; its scalar x2-fibre must preserve the standard normal law. The scalar argument gives exactly identity or the global reflection (x1,x2)↦(x1,−x2). Its connected identity component is still trivial. Failure of (4) is therefore not proof of nonrigidity.

## 6 Genuine multidimensional nonrigidity

### Rotating a Gaussian block by its base

Let X∈R² have law N(0,σ_c²I2) in each context c, independent of a scalar full-support base U. For nonconstant smooth φ,

\[
 v(x,u)=(Q_{\phi(u)}x,u),\qquad
 v^{-1}(y,u)=(Q_{-\phi(u)}y,u), \tag{7}
\]

where Q is a planar rotation. Every block law is rotation invariant, so (7) preserves every corresponding product law. Its output scalar coordinates are independent too, because the output joint law is exactly the same isotropic Gaussian product. This is a genuine nonlinear triangular equivalence, not a support-only shear. The likelihood-ratio gradients are radial and have rank at most one.

This also gives an exact S26 counterexample to universal block-diagonal rigidity, even under sufficient auxiliary influence. Take T=1, one real action a, true density

\[
 (X_1,X_2,U)\mid a\sim N(0,I_2)\otimes N(a,1),
 \qquad G^a=(0,0,1)^\top.
\]

The mixed action-score column is (0,0,1)^T, satisfying Assumption 6; finite action-score differences satisfy Assumption 7. Take the true emission map to be identity and the learned emission map to be v from (7), with the same Gaussian measurement-noise law. The latent product laws are unchanged under v, so the observation laws agree. Both maps are global smooth diffeomorphisms, all densities are smooth and positive, and the action graph is unchanged. The unacted SCC {1,2} can depend on the acted scalar base {3}. This example does not challenge Theorem 3 or the acted-on-block corollaries below; its two-dimensional block has no incoming action influence.

### Non-Gaussian single-law symmetries are also abundant

The Gaussian example is not an isolated accident of covariance. Let ρ be any positive C∞ probability density on R^m, m≥2. Choose a nonconstant compactly supported C∞ function ψ and set

\[
 W=\rho^{-1}(\partial_2\psi,-\partial_1\psi,0,\ldots,0).
\]

This is a smooth compactly supported vector field and div(ρW)=0. Its complete flow F_s preserves ρ(x)dx: differentiation of ρ(F_s(x))det DF_s(x) gives div(ρW)(F_s(x))det DF_s(x)=0. Thus T_u=F_{φ(u)} provides nontrivial smooth base dependence preserving that one law. If ρ itself is a scalar product density, the complete output law remains that product density. Multiple context laws restrict this freedom through their **common** stabilizer; a single initialization does not generally remove it in dimension at least two.

## 7 Deriving block rigidity from the S26 influence assumptions

The exact source support and initialization checks are recorded in `Source_Clarification_Initialization_and_Residual_Preorder.md`. Source references are [Assumptions 2 and 4](https://arxiv.org/html/2401.04890v2#S2.SS1), [Definition 7 and Proposition 8](https://arxiv.org/html/2401.04890v2#S2.SS4), and [Assumptions 6–8](https://arxiv.org/html/2401.04890v2#S3.SS8). The following conclusions are derived here, not quoted as statements of that paper.

### Orientation and contexts

After the source's aligned permutation, its entanglement map is c from aligned learned states to true states. Apply Sections 2–5 to r=c^{-1}. Then the source measures in (2) are the **true** conditional factors, where the source variability assumptions hold. The target factor uses the transformed past r(h). Both r and c respect the same residual preorder because graph-preserving diffeomorphisms form a group.

For every true context h=(t,z^{<t},a^{<t}), the diffeomorphism-equivalence equation transports the full product conditional law. Theorem 1 applies because every conditional factor has full support. Consequently the relative fibre maps of r_B preserve the entire family

\[
 \mu_B^h(dx_B)=\prod_{i\in B}p_i^t(x_i\mid z^{<t},a^{<t})\,dx_B.
\]

Let s_B(x_B;h)=∇_{x_B}log p_B^h(x_B) wherever the density is positive. Define W_B(x_B) as the linear span of all differences s_B(x_B;h)-s_B(x_B;h') for contexts positive at x_B. This is exactly the span of local log-ratio gradients. Being a linear subspace of finite-dimensional R^{d_B}, it is closed.

### Auxiliary influence

For an SCC of the action or combined residual preorder, all coordinates in B have the same action-parent set. If this set contains ℓ, projection of the source Assumption 7 score-difference span onto B is all R^{d_B}. Each projected vector belongs to W_B(x_B). Thus W_B(x_B)=R^{d_B} at the projected good current states.

Under Assumption 6 the projected vectors are derivatives of s_B with respect to an earlier action coordinate. At an interior admissible context where the source log density is defined, each derivative is a limit of admissible score differences divided by a scalar; hence it lies in W_B(x_B). If a witness context is on the auxiliary boundary, regular-closed support provides a sequence of interior contexts approaching it. Positivity at the log-density witness persists in a neighborhood, and C² regularity makes the mixed-score derivatives continuous there. The boundary derivative is therefore also a limit in the same closed space W_B(x_B).

Projection of the source's full-measure good current-state set is dense in block space. At every projected point the previous argument gives full ratio rank. Theorem 3 eliminates all strict-base dependence into B.

### Temporal influence

For an SCC of the temporal or combined residual preorder, all coordinates in B have the same temporal-parent set. If it contains j, the linear map that selects column j of a matrix and then its rows B maps R_{G^z}^{d_z×d_z} onto R^{d_B}. Applying it to the Assumption 8 spanning family yields vectors spanning R^{d_B}.

Each vector is a derivative of s_B(x_B;h) with respect to a past coordinate z_j^τ. It belongs to W_B(x_B) by a difference-quotient limit, since latent-history space is all Euclidean space and the witness log density is locally positive. Assumption 8 requires the **selected original witness** to obey z^τ=z. The nearby contexts used in the difference quotient need not retain this equality: the common stabilizer already preserves every conditional context, not just the selected spanning witnesses. Thus there is no illicit differentiation of the diagonal constraint.

Again, the projected good current states are dense, so Theorem 3 eliminates strict-base dependence into B.

### Scope of these source corollaries

- Every singleton SCC is rigid from one full-support product initialization, regardless of whether it has parents.
- A higher-dimensional SCC with an incoming auxiliary parent is rigid under the corresponding Assumption 6 or 7.
- A higher-dimensional SCC with an incoming temporal parent is rigid under Assumption 8.
- Multidimensional blocks with neither such certified incoming influence may retain common symmetries, as (7) demonstrates.
- If source log-score expressions are invoked, they must actually be defined at their chosen witnesses. The proof never infers pointwise positivity everywhere from “full support.” It uses only positivity at those finite witnesses and local continuity.
- These statements eliminate **current-coordinate representation base dependence**, not temporal interaction between different learned blocks. They do not turn interacting mechanisms into autonomous components.

## 8 Moment free affine block rigidity and S22

A random vector X_C is affinely nondegenerate when no nonzero row vector a makes aX_C almost surely constant. This is weaker than having a density or positive covariance; covariance need not exist.

### Lemma 4

A Borel probability measure η on R^m has no nonzero translation symmetry.

**Proof.** If translation by a preserves η, its characteristic function satisfies φ(t)=e^{it·a}φ(t). Continuity and φ(0)=1 imply φ is nonzero in a neighborhood of zero. Hence e^{it·a}=1 throughout that neighborhood, which forces a=0. ∎

### Theorem 5

Let X_1,…,X_k be independent, affinely nondegenerate random vectors. Let

\[
 Y_B=A_{BB}X_B+\sum_{C\in U(B)}A_{BC}X_C+b_B
\]

be an invertible block-triangular affine transformation. If Y_1,…,Y_k are independent, then A_{BC}=0 for every strict pair C∈U(B). Thus A is block diagonal.

**Proof.** Its diagonal blocks and upper-closed restrictions are invertible. Therefore σ(Y_U)=σ(X_U) for U=U(B). Independence of Y_B from Y_U means that the conditional law of Y_B given X_U=u is constant for almost every u. But this law is the fixed probability law η_B of A_{BB}X_B translated by

\[
 g(u)=\sum_{C\in U(B)}A_{BC}u_C+b_B.
\]

For two bases from the full-measure conditional set, their translates of η_B coincide; Lemma 4 gives equal shifts. Hence g(X_U) is almost surely constant.

The independent random vectors Z_C=A_{BC}X_C have a constant sum. Each Z_C must be constant: it is independent of the sum of the other terms, but also is a measurable function of that sum. Thus it is independent of itself, which forces its law to be a point mass. Affine nondegeneracy of X_C then implies every row of A_{BC} is zero. ∎

This proof never forms a covariance matrix. It applies to heavy-tailed variables and disconnected or discrete supports. Conversely, block-diagonal invertible affine maps always preserve block independence, though any required matching of specific target factor laws remains an additional constraint.

If the coordinates inside a block are independent nondegenerate scalars, the block is affinely nondegenerate: an almost surely constant nontrivial linear combination would, by the same independent-summands argument, make one of those scalars degenerate. This is the hypothesis needed for scalar sufficient statistics.

The nondegeneracy condition is substantive. If X_C=(Z,Z), a nonzero row (1,−1) vanishes on its support. A triangular matrix can include that off-block row without changing any random output. No law-based argument can recover a coefficient invisible on the entire support.

### Applying the theorem to S22

S22 Theorem 5 uses one scalar sufficient statistic per coordinate and assumes the stacked coordinatewise statistic map is a diffeomorphism. Its Theorem 4 gives a **constant affine** relation in statistic space. The source proof, after its matched permutation P, supplies M=LP with support in the preorder of componentwise inclusions of the signatures (Pa^a,Pa^z,Ch^z). The SCCs are the equal-signature classes; the matched diagonal is nonzero and the block-triangular matrix is invertible.

The actual trajectory equivalence transports initialization, not merely later transitions. At a fixed admissible initial action, scalar statistics are independent in both models. Minimality of the scalar statistic and the context-independent exponential-family support imply nondegeneracy under this initial law: multiplying the fixed base measure by a finite positive exponential factor cannot turn a nonconstant statistic into an almost surely constant one. Theorem 5 therefore forces M to be block diagonal across equal-signature classes.

Consequently **distinct signatures suffice for componentwise recovery in this affine-statistic setting**, even if the signatures are comparable. The source graphical singleton-intersection condition is the stronger antichain condition. This conclusion uses the source's staged graph-support proof and actual initialization transport; it is not inferred from graph equality alone. See the exact source reconstruction and equation pointers in `Source_Clarification_Initialization_and_Residual_Preorder.md`; the primary source is [Lachapelle et al. 2022, Theorems 4–5 and Appendices A.2–A.3](https://proceedings.mlr.press/v177/lachapelle22a/lachapelle22a.pdf).

Inside an equal-signature block, affine independence can permit genuine mixing, e.g. orthogonal mixing of independent equal-variance Gaussians. Classical linear ICA can add further within-block conclusions under appropriate non-Gaussianity hypotheses; those are separate from the theorem just proved. Comon's original treatment is [*Independent Component Analysis, a new concept?*](https://www.sciencedirect.com/science/article/pii/0165168494900299); Hyvärinen and Oja discuss the Gaussian ambiguity in their [author-hosted primary article](https://www.cs.helsinki.fi/u/ahyvarin/papers/NN00new.pdf). We do not invoke a Darmois–Skitovich theorem, finite-moment expansion, or generic non-Gaussianity to establish the strict off-block zeros.

## 9 A growing same assumption S22 example beyond the antichain criterion

For each n≥2, use n latent coordinates and n real auxiliary coordinates, horizon T=2, scalar statistic s_i(z_i)=z_i, and unit-variance Gaussian conditional factors. Write their natural parameters as

\[
 \lambda_i^1(a^0)=\sum_{\ell\le i}(a_\ell^0)^{i+1},
\]

\[
 \lambda_i^2(z^1,a^{<2})
 =\sum_{j=1}^{n}(z_j^1)^{i+1}
  +\sum_{\ell\le i}(a_\ell^1)^{i+1}. \tag{8}
\]

Take any globally invertible smooth observation mixing, for example f(z)=Qz with a dense nonsingular Q, and the source's fixed Gaussian measurement noise. The base measure is standard Gaussian and ψ_i(λ)=λ²/2. Every conditional law has full support, all functions are smooth, and the scalar statistic is minimal and a diffeomorphism.

The true temporal graph G^z is fully dense. The action row of i is {1,…,i}. Therefore all temporal row/column signatures are identical, while action signatures are strictly nested and distinct. The combined residual preorder is a total order with singleton SCCs but is not an antichain.

All source variability spans can be checked explicitly:

1. **Natural-parameter variability.** At time 2 with actions zero, compare z^1=0 with z^1=s_r e_1 for n distinct positive values s_r. The difference vectors have entries s_r^{i+1}. Their matrix is an ordinary Vandermonde matrix multiplied by nonzero column factors s_r², so it has rank n.
2. **Temporal sufficient influence.** For each past coordinate j, choose z^1=s_r e_j and zero actions. The Jacobian D_{z^1}λ has only column j nonzero, with entries (i+1)s_r^i. The n positive distinct s_r give rank n in that column. Over all j these n² witnesses span all n×n matrices, exactly R_{G^z}.
3. **Action sufficient influence.** For auxiliary ℓ, change its value from zero to ε_r, holding all other inputs at zero. The natural-parameter difference has entries ε_r^{i+1} for i≥ℓ and zero otherwise. Use n−ℓ+1 distinct positive ε_r. Factoring ε_r^{ℓ+1} leaves a Vandermonde matrix, so these vectors span exactly the allowed child coordinates.
4. **Initialization.** At a0=0 the initial law is the independent standard Gaussian product. Any exact-fit comparison model in the source class also has a product initial law.

Therefore the source's staged graph inclusions and sparsity premise apply, and Theorem 5 above turns the resulting constant triangular statistic mixing into a diagonal one after the matched permutation. This verifies a genuinely interacting growing family where the antichain criterion fails but the sharpened conclusion is componentwise.

The family is spatially **dense**, with O(n²) temporal edges. It is not a certificate of bounded local wiring, sparse physical ports, finite-data recovery, or a resource-efficient implementation. Those are separate targets of the learned-interface bridge.

## 10 Integration boundary and review checklist

The bridge may use these results to replace an overly large graph-preserving support envelope by a smaller class of actual law equivalences. It may then organize learned coordinates, SCC blocks, invariant interfaces, and chart changes using that smaller class. It may not infer any of the following without another argument:

- that all support-allowed shears are observational equivalences;
- that a block is temporally autonomous merely because its representation change has no strict-base dependence;
- that coordinate ambiguity reduction discovers physical message channels or their bandwidth;
- that an exact-law identifiability statement supplies finite-sample optimization or coverage guarantees;
- that the generic transport lemmas are new mathematical discoveries.

Checks completed in this note: global fibre invertibility; conditional disintegration; a.e.-to-everywhere upgrade; scalar orientation; density zeros; connected versus disconnected symmetry; source-map orientation; boundary auxiliary derivatives; temporal diagonal-witness differentiation; moment-free affine nondegeneracy; and a coupled growing S22 witness family. The source hypotheses and exact equation locations are separately cross-checked by the translation note.
