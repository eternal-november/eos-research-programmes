# Independent challenge of the affine bundle factorization theorem

**Supplement snapshot:** contextual research material, not exact-hash-certified against the final circle review. The final report in the package root takes precedence. See ../SOURCE_STATUS.md.

Date: 2026-11-03. Scope: independently audit the proposed theorem, attack continuity and positivity loopholes, compare primary prior art. This is a mathematical audit, not a novelty certification.

## Verdict

No counterexample found to the proposed exact theorem after making `0 < epsilon`, `m >= 2`, and nonempty base explicit. The lower bound is stronger than originally stated: continuity of either one of the two factors is sufficient, even for unnormalized nonnegative factors. A direct quantitative argument also gives a uniform approximation gap with only one factor continuous, without any rank promise or separate continuity promise on the product. The upper bound can use strictly positive factors. The S² example separates continuous positive/stochastic width 4 from continuous unconstrained real width 3.

The closest located primary prior art includes Mond–Smith–van Straten on topology of stochastic factorization spaces, Hrubeš on a positive rank-one baseline reducing pointwise nonnegative rank, and universality results for NMF and nested-polytopes solution spaces. These mean neither “topology matters for stochastic factorization” nor the pointwise baseline construction should be claimed as new. No located source states the precise bundle embedding-width formula below, but this search does not establish novelty.

## 1. Exact statement and conventions

Let X be a nonempty topological space, m >= 2, n=m-1, W=1_m^perp in R^m, and E a continuous rank-r vector subbundle of X×W. Fix an m×n isometry Q with columns a_1,...,a_n forming an orthonormal basis of W. Let P_x be orthogonal projection onto E_x. Fix

    0 < epsilon < 1/(mn).

Let H_x be the m×m matrix with rows

    H_0(x)=c^T,      H_i(x)=c^T + epsilon a_i^T P_x,  1<=i<=n,
    c=(1/m)1_m.

Let s be the least integer t for which E embeds as a vector subbundle of X×R^t. Since E is already a subbundle of X×W, s<=n. For r=0, set s=0 and all factor widths below equal 1.

For r>0:

1. H is continuous, strictly positive, and row-stochastic.
2. Every H_x has ordinary, nonnegative, and stochastic factor width r+1.
3. The minimum global labelled width with both stochastic factors continuous is s+1.
4. The same minimum s+1 holds for both-continuous entrywise nonnegative factors, without any stochastic normalization requirement.
5. In fact, any exact H=UV with V entrywise nonnegative and at least one of U,V continuous has width k>=s+1. U need not be nonnegative for this lower bound.
6. A width-(s+1) factorization exists with both factors continuous, row-stochastic, and strictly positive.

Compactness is not needed for these statements once the finite-dimensional bundle embedding is given. Compact Hausdorff X is a harmless standard hypothesis, but none of the proofs below uses compactness. Width zero is excluded by the nonzero stochastic rows. Empty X or m=1 should be handled separately rather than allowed to make the formulas ambiguous.

## 2. Rank and elementary positivity

Let D_H have rows H_i-H_0, i=1,...,n. Then

    D_H = epsilon Q^T P,
    D_H e = epsilon Q^T e,
    D_H^T Q^T e = epsilon e       (e in E).

Thus its row space is exactly E, and the row space of H is span(c) direct-sum E. The two summands are orthogonal, so rank(H)=r+1. Each row sums to 1 because E⊂W. Each entry differs from 1/m by at most epsilon; consequently it is positive. The stronger epsilon<1/(mn) is used for the simplex construction, not merely for positivity.

## 3. Global upper bound with positive factors

Choose a bundle embedding E→R^s and polar-normalize it to a continuous fibrewise isometry J_x:E_x→R^s. This uses the positive definite operator (j_x^*j_x)^(-1/2), which is continuous. Let q_1,...,q_(s+1) be unit regular-simplex vertices in R^s, so

    sum_j q_j=0,
    sum_j q_j q_j^T=((s+1)/s) I_s.

Choose a constant beta with

    s epsilon < beta < 1/m.

This is possible since s<=n. Define decoder rows and encoder coefficients by

    B_j = c^T + beta (J_x^* q_j)^T,
    A_0j = 1/(s+1),
    A_ij = [1 + (s epsilon/beta) <q_j,J_x P_x a_i>]/(s+1).

The simplex identities give AB=H and row sums 1. Since |<q_j,J P a_i>|<=1, every A_ij >= (1-s epsilon/beta)/(s+1)>0. Every B_jℓ >= 1/m-beta>0. This proves the global upper bound, including strict positivity of both factors. Applying the same construction at a single x with s replaced by r proves pointwise width r+1; rank supplies the matching lower bound.

## 4. Exact lower bound: continuity in either channel

Suppose H=UV with U m×k, V k×m, V>=0, and no continuity assumption on the other factor beyond the channel being considered. Write D_U for the n×k matrix with rows U_i-U_0. Put d=V1_m. Then

    d>=0, d!=0, U d=1_m, D_U d=0, D_U V=D_H.

The vector d is nonzero because U d=1_m. Let Pi_k be orthogonal projection onto 1_k^perp.

### 4a. U continuous; V can be arbitrary

Define the continuous bundle map

    J_U(e)=Pi_k D_U^T Q^T e  : E→X×1_k^perp.

If J_U(e)=0, then D_U^TQ^Te=lambda 1_k. Taking dot product with d gives

    0=(Q^T e)^T D_U d=lambda <1_k,d>.

Because <1_k,d>>0, lambda=0. Multiplying by V^T gives epsilon e=0. Thus J_U is fibrewise injective and E embeds in the trivial rank-(k-1) bundle. In particular s<=k-1.

No projector onto an image bundle, no global choice of V-row normalization, and no continuity of d are needed in this proof.

### 4b. V continuous; U can be arbitrary

Now d is continuous. Define P_(d^perp)=I-dd^T/||d||² and

    J_V(e)=Pi_k P_(d^perp) V e.

The map Pi_k restricted to d^perp is injective, because its kernel would consist of a multiple of 1_k perpendicular to d, impossible unless the multiple is zero. If J_V(e)=0, it follows that Ve=lambda d. Therefore

    epsilon Q^T e=D_H e=D_U Ve=lambda D_Ud=0.

Again this is a continuous fibrewise injection E→1_k^perp. This handles all zero rows of V.

### 4c. Simpler stochastic special cases

If U=A and V=B are row-stochastic, d=1_k. For A-continuity the projection Pi_k can be omitted because D_A1_k=0. For B-continuity use Pi_k B|_E. Either alone gives the same lower bound.

## 5. Why naive normalization at zero rows is a real trap

For an exact nonnegative factorization with both factors continuous, d=V1 is continuous and A=U diag(d) is continuous row-stochastic. Normalize a V row when d_j>0 and choose any probability row when d_j=0. The resulting B need not be continuous, but AB=H still holds and the A-only stochastic lower bound is enough.

Continuity failure is not hypothetical. On t∈[0,1/4], let q(t) be a probability vector in R² oscillating as sin(1/t), let q(0) be arbitrary, and define

    V_2(t)=t q(t),  V_1(t)=c-t q(t),  U_i=(1,1) for every row i,
    c=(1/2,1/2).

Both U and V are continuous and nonnegative, and UV has every row c. But V_2/(V_2 1)=q(t) has no limit at zero. One must not assert that row normalization preserves continuity of both factors.

## 6. Uniform approximation without a rank promise

Use the entrywise supremum norm over X, and write delta=||G-H||_infty. For any product G=UV, let D_G have rows G_i-G_0. Then

    ||D_G-D_H||_op <= 2 sqrt(nm) delta.            (1)

### 6a. Stochastic factors: sharper radius

If A,B are stochastic and at least one is continuous, the injectivity arguments in §4c survive whenever

    delta < epsilon/(2 sqrt(nm)).                (2)

For example, a kernel vector of D_A^TQ^T|_E would make D_G^TQ^Te=0, contrary to (1) and D_H^TQ^Te=epsilon e. The B-side argument is analogous. No assumption on rank(G), constancy of its rank, or even its continuity is needed if only one factor is continuous.

### 6b. Nonnegative factors: direct one-channel radius

A stronger-than-needed version is valid: suppose V>=0, U arbitrary real, and at least one of U,V is continuous. If

    delta < epsilon/(2 m sqrt(n)),               (3)

then E embeds in the trivial rank-(k-1) bundle. Thus a width k<=s product cannot approximate H within that radius. Neither G-stochasticity, rank(G), nor continuity of G itself is assumed.

Proof when U is continuous: use J_U(e)=Pi_k D_U^TQ^Te as in §4a. If J_U(e)=0 for nonzero e, then

    D_G^TQ^Te=lambda V^T1_k

lies in the nonnegative or nonpositive orthant. Every e∈W satisfies

    dist(e,R^m_+) >= ||e||/sqrt(m),
    dist(e,-R^m_+) >= ||e||/sqrt(m).              (4)

Indeed, writing e=e_+-e_-, the two parts have equal l1 norm t; since each has support at most m-1, ||e_+||²<=t²<=(m-1)||e_-||², and conversely. Therefore each part has norm at least ||e||/sqrt(m). Equation (1) now contradicts (4) under (3).

Proof when V is continuous: d=V1 is continuous and nowhere zero. Otherwise V=0 at that point, G=0, and delta>=1/m from H_0=c, contradicting (3). Use J_V as in §4b. If it has a nonzero kernel vector e, then Ve=lambda d. At least one row of V has positive row sum, so lambda is a convex average of the coordinates of e. Since e⊥1_m,

    |lambda| <= max_j|e_j| <= sqrt((m-1)/m)||e||,
    ||e-lambda 1_m|| <= sqrt(m)||e||.

Also D_G(e-lambda 1_m)=0, whereas D_H(e-lambda 1_m)=epsilon Q^Te. By (1),

    epsilon||e|| <= 2 sqrt(nm)delta sqrt(m)||e||,

contradicting (3). This completes the direct one-channel robust proof.

### 6c. Safe but weaker normalization alternative

If BOTH nonnegative factors are continuous, or enough is separately known to ensure continuity after dividing U's rows by G's row sums, one can normalize G's rows. For delta<1/m,

    ||G_normalized-H||_infty <= (m+1)delta/(1-m delta).

Combining with (2) gives the weaker sufficient radius

    delta < epsilon/[2 sqrt(nm)(m+1)+epsilon m].

This normalization proof must not silently be promoted to a one-channel theorem. The direct proof in §6b supplies that theorem independently.

## 7. The S² separation, with an explicit real factorization

Take m=4,n=3 and identify W with R³ by Q. Let x∈S² and P=I_3-xx^T. Then E_x=Q x^perp is isomorphic to TS². Its least embedding dimension is 3: it already embeds in R³, whereas an embedding into R² would trivialize the rank-2 tangent bundle, contradicting the hairy-ball theorem.

Consequently pointwise stochastic/nonnegative width is 3, and global continuous labelled stochastic/nonnegative width is 4. On the other hand E⊕1 is trivial, and the unconstrained real width is exactly 3.

Here is a direct factorization, so the latter claim does not depend on abstract stable triviality. Let e_0=(1/2)1_4. Define A_real with rows

    (A_real)_0=x^T/2,
    (A_real)_i=x^T/2+epsilon e_i^T P,  1<=i<=3,

and define

    B_real=x e_0^T + P Q^T.

Then A_real B_real=H because Px=0 and x^Tx=1. Both factors depend smoothly on x. Rank(H)=3 makes width 3 minimal.

For epsilon=1/24 the stochastic exclusion radius (2) is approximately 0.0060141, and the one-channel nonnegative exclusion radius (3) is approximately 0.0030070 in entrywise sup norm. These are explicit lower bounds on approximation error, not claims of an optimal error threshold.

## 8. Labelled versus unlabelled latent states

The fixed labelling condition matters in general. For the Möbius line bundle over RP¹, two unordered endpoints c±beta v give a continuous unordered two-point decoder, even though a continuous labelled width-2 realization is obstructed; locally choosing v swaps the two labels around the loop. This does not refute the theorem as stated.

For S² at width 3, even an unordered rank-size factorization would lift to a labelled one: permutations act freely on rank-size factors and S² is simply connected. Thus the S² obstruction is not merely a label-swapping loop artifact. This statement concerns the ordinary quotient by a finite label permutation group with its usual topology, not more general latent bundles or arbitrary measurable conventions.

## 9. Primary prior-art comparison

### Mond, Smith, van Straten (2003)

“Stochastic factorizations, sandwiched simplices and the topology of the space of explanations,” Proceedings of the Royal Society A, DOI [10.1098/rspa.2003.1150](https://doi.org/10.1098/rspa.2003.1150). [Author-hosted PDF](https://download.uni-mainz.de/mathematik/Algebraische%20Geometrie/DvS-Publikationen/30.Stochastic%20factorizations,%20sandwiched%20simplices%20and%20the%20topology%20of%20the%20space%20of%20explanations%20-%202003.pdf).

Theorem 2.4 identifies rank-size stochastic factorization spaces with spaces of ordered sandwiched simplices; Corollary 2.5 handles the label-permutation quotient. Section 3 studies homotopy types; Proposition 3.1 treats rank 2, and Section 4 rank 3. This is the strongest directly relevant conceptual antecedent located. It studies the topology of the fibre over a fixed stochastic matrix. The proposed theorem instead identifies the minimal width of a continuous section over a chosen parameter space with a vector-bundle embedding invariant. That distinction is mathematically meaningful, but does not by itself establish novelty.

### Hrubeš (2020)

“On epsilon-sensitive monotone computations,” Computational Complexity 29:6, DOI [10.1007/s00037-020-00196-6](https://doi.org/10.1007/s00037-020-00196-6). [Author PDF](https://users.math.cas.cz/~hrubes/PDFs/Epsilon.pdf).

Lemma 3.9 states that if V is positive rank one, then for sufficiently large t, rank_+(N+tV)<=rank(N)+1. Thus a large positive baseline making pointwise nonnegative rank essentially ordinary rank is established prior art. Sections 3.2–3.3 also discuss continuity of nonnegative rank and strictly positive factorizations. The explicit uniform regular-simplex constant and the global bundle obstruction are not supplied by that lemma.

### Shitov and Dobbins–Holmsen–Miltzow

Shitov, [“A universality theorem for nonnegative matrix factorizations”](https://arxiv.org/abs/1606.09068), and Dobbins, Holmsen, Miltzow, [“A Universality Theorem for Nested Polytopes”](https://arxiv.org/abs/1908.02213), show universality of corresponding normalized solution spaces. These are important prior art for the possible topological complexity of NMF solutions. Their abstract statements concern realization of spaces of solutions, not the exact minimum continuous width over an arbitrary externally prescribed bundle base. They prevent broad claims that topological NMF obstructions or rich factorization-space topology were previously unknown.

### Ke, Montiel Olea, Nesbit (2024)

[“Robust machine learning algorithms for text analysis”](https://doi.org/10.3982/QE1825), Quantitative Economics 15, 939–970; [Appendix A of the supplement](https://joseluismontielolea.com/OnlineAppendix_LDA_2024.pdf).

Appendix A discusses upper and lower hemicontinuity of the exact column-stochastic NMF correspondence, to obtain continuity of optimization value functions. This is relevant family-continuity literature. A continuous set-valued correspondence is not a continuous single-valued global choice, and therefore does not defeat the bundle obstruction. Its proof uses rank-size/full-rank assumptions; do not quote it as an unrestricted global selection theorem. I did not audit all its boundary claims, and the present theorem does not depend on them.

### Gubeladze (2016/2019)

[“Affine-compact functors”](https://arxiv.org/abs/1608.04177), especially Section 8, develops sandwiching and complementing functors motivated by Mond–Smith–van Straten. This is adjacent affine/convex structural work. The inspected text contains no vector-bundle embedding-width theorem.

### Krylov (2007/2008)

[“On factorizations of smooth nonnegative matrix-values functions and on smooth functions with values in polyhedra”](https://arxiv.org/pdf/0706.0192), Applied Mathematics and Optimization 58, 373–392, DOI [10.1007/s00245-008-9040-2](https://doi.org/10.1007/s00245-008-9040-2).

Here “nonnegative symmetric matrices” means positive semidefinite matrices. The paper starts with u=vv* and seeks representations by fixed directions gamma_k with nonnegative scalar weights and Lipschitz square roots. Formula (1.5) provides smooth positive barycentric coordinates in the interior of a fixed polyhedron. This is relevant continuous convex-decomposition background, but is not an entrywise NMF minimal-width or vector-bundle obstruction theorem. Do not infer direct overlap from its title alone.

## 10. Numerical independent check

The accompanying `affine_independent_checks.py` samples 10,000 points on S², using a Helmert isometry Q, epsilon=1/24, and beta=3/16. It checks the positive width-4 simplex factors, the explicit real width-3 factors, row sums, rank, and the orthant-distance inequality. Results are in `affine_independent_checks.json`.

Maximum product errors were 1.2e-16 for the stochastic construction and 3.1e-16 for the real construction. Minimum sampled factor entry was about 0.0928. The numerical checks validate formulas and dimensions, not the topological impossibility or novelty claim.

## Remaining limitation

This is not an exhaustive literature review. No source located in the targeted search establishes the exact equality between continuous labelled stochastic width and one plus the embedding dimension of E. The appropriate claim is “an independently checked theorem with close precedents identified,” pending specialist literature review, not “a novel theorem.”
