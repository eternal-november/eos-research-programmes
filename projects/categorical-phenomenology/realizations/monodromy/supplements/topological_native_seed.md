# Observable bundles and continuously labelled stochastic realizations

**Supplement snapshot:** contextual research material, not exact-hash-certified against the final circle review. The final report in the package root takes precedence. See ../SOURCE_STATUS.md.

**Research status, 3 November 2026.** Research proof note with accompanying mathematical reviews. This is not a novelty claim. The bundle obstruction, its projective-space growth, and the distinction between local and global matrix realizations have strong classical predecessors, including Swan and Hazewinkel. The most informative additional comparison here is a precise difference between continuous **unconstrained real** and **normalized affine/stochastic** factorization on the tangent bundle of the two-sphere. The gap is not caused by positivity alone: signed models with a fixed terminal functional obey the same normalized lower bound. Section12 gives an explicit all-horizon contracting construction for arbitrary observable bundles; Section6 separately gives a noncontracting sign-cover construction. Their action timing and native comparisons differ.

## 1. What is supplied and what is reconstructed

The input is a continuous, finitely presented family of finite stochastic response tables over a specified parameter space X. Compact Hausdorff bases cover the examples, but the theorems below need no compactness once the indicated finite-dimensional continuous subbundles and embeddings exist. Preparations and output labels are globally fixed. The parameter topology and continuity requirement are supplied, not learned from finitely many response records.

The output reconstructed from the table is its centered response bundle E: at each parameter, take the linear span of differences between preparation response distributions. It is a vector bundle when that dimension is constant. This object can be recovered without choosing latent labels. Its bundle embedding dimension gives a lower bound on the number of **globally named**, continuously varying latent states.

The reconstruction does not say that a particular hidden carrier is uniquely identified. Nor does it require one to use fixed global labels: allowing local labels with transition identifications is a different native category and can remove the obstruction. Continuity must be a real modeling requirement, for example a device operated continuously across a parameter family, not imposed after seeing a favorable example.

## 2. A general normalized factorization obstruction

Let H:X→R^{p×m} be continuous and row stochastic. Choose one distinguished preparation 0 and suppose

    E_x = span{H_i(x)−H_0(x): i=1,…,p−1}

has constant dimension r. Every E_x lies in W={z∈R^m: Σz_j=0}. Write g(E) for the least s such that E embeds as a vector subbundle of X×R^s. A metric adjoint identifies this with the least s admitting a continuous surjection X×R^s→E.

**Proposition 1.** If H=UV pointwise, where U is row stochastic of size p×k and V is row stochastic of size k×m, and V is continuous, then

    k ≥ g(E)+1.

Continuity of U is not needed for this conclusion.

**Proof.** Restrict V(x)^T to 1⊥⊂R^k, then orthogonally project its image onto E_x. This is a continuous map T_x:1⊥→E_x. Each H_i−H_0 equals (U_i−U_0)V, with U_i−U_0∈1⊥, so E_x is contained in the image of V(x)^T|1⊥. Consequently T_x is onto. Its adjoint embeds E into the trivial rank-(k−1) bundle. ∎

A corresponding preparation-only statement uses the centered **column** bundle of the table. It is not automatically the same E for every arbitrary table, but it is isomorphic to E under a constant-rank table and canonical row/column duality. The projection family below makes that isomorphism explicit.

This lower bound is an affine/bundle obstruction. Positivity is not used beyond the normalized affine factorization equations. It must not be described as a new phenomenon caused by nonnegative entries alone.

## 3. An explicit family attaining the bundle bound

Let m≥2, n=m−1, c=(1/m,…,1/m), and W=1⊥⊂R^m. Choose an orthonormal basis a_1,…,a_n of W. Let E⊂X×W be a positive-rank continuous subbundle, with orthogonal projection P_x. Assume X is nonempty. The rank-zero case has H_i=c and minimum width one in every category; below r>0. Fix

    0 < β < 1/(mn).

Define the m×m response family by

    H_0(x)=c,
    H_i(x)=c+β P_x a_i,     i=1,…,n.                         (1)

Every row sums to one. Its entries are strictly positive because |(P_xa_i)_j|≤1 and β<1/m. The centered response bundle is exactly E: the projection rows span the range of P_x. The baseline c is essential; omitting it can make a naive projection-row construction lose rank.

**Equivalent input-level recognition.** One need not receive E as a named latent object. Given a continuously presented stochastic H with baseline H_0=c, form D=CHA using the fixed matrices below. Check that D/β is symmetric, idempotent, and of constant rank. Its image defines E (transported into W by A), and reconstructs exactly the projection presentation(1). These are equations and rank conditions on the input table. The examples build such tables from familiar bundles to make their topological invariants computable; this is not a claim to discover the supplied parameter topology from a finite cloud of samples.

**Theorem 2.** For the family (1), if E has rank r and g(E)=s, then:

1. rank H(x)=rank_+ H(x)=r+1 at every x;
2. the minimum size of a globally continuous row-stochastic factorization is exactly s+1;
3. the same lower bound holds if only the preparation factor is continuous, or if only the readout factor is continuous.

Here rank_+ is ordinary pointwise nonnegative rank. The theorem concerns a family of finite tables, not yet a temporal mechanism.

**Pointwise rank.** The differences span E_x and c∉W, so row rank is r+1. To obtain the matching positive factorization, choose any orthonormal coordinates on E_x and a sufficiently small enclosing r-simplex centered at c. The quantitative construction below with s replaced by r supplies it. Thus this is not an unsupported assertion that every rank-(r+1) nonnegative matrix has nonnegative rank r+1.

**Global upper bound.** Choose an isometric bundle embedding j:E→X×R^s; a continuous embedding can be made isometric using the inverse square root of its fiberwise Gram operator. Since E already embeds in W, s≤n. Let z_1,…,z_{s+1} be vertices of a regular unit-radius simplex in R^s:

    Σ_j z_j=0,   z_i·z_j=−1/s  (i≠j),
    Σ_j z_jz_j^T=(s+1)I/s.

Choose nβ<δ<1/m. Write R_x:R^s→W for inclusion∘j_x^*, and put

    V_j(x)=c+δ R_x z_j,
    t_i(x)=(β/δ)j_xP_xa_i,
    U_ij(x)=[1+s z_j·t_i(x)]/(s+1),
    U_0j(x)=1/(s+1).                                      (2)

The rows of U and V sum to one. V is strictly positive since ||R_x||≤1 and δ<1/m. U is strictly positive since s||t_i||≤sβ/δ<1. The simplex identity gives Σ_j U_ij z_j=t_i and R_xt_i=(β/δ)P_xa_i. Therefore UV=H. All maps are continuous; if the bundle and embedding are smooth, these factors are smooth.

**Readout-only lower bound.** Apply Proposition 1.

**Preparation-only lower bound.** Let A:R^n→W have columns a_i, identify E with F=A^TE⊂X×R^n, and set C=[−1_n I_n], so C has n rows and m columns. Then

    D(x):=C H(x) A=β A^TP_xA=β P_{F_x}.                   (3)

For a factor H=UV, B=CU is continuous when U is, B1_k=0, and D=BVA. Its image is F_x, contained in im B_x. Thus P_{F_x}B_x restricted to 1⊥⊂R^k is onto F_x. Its metric adjoint gives the required embedding. No continuity of V was used. ∎

**Unnormalized nonnegative factors, including one-factor continuity.** The minimum s+1 also holds for H=UV with U,V≥0 not required to be stochastic, when either original factor is continuous. In fact the lower bound needs V≥0 but allows U to have arbitrary real entries. Put d=V1≥0, which is nonzero at every parameter, and B=CU. Because H1=1, Bd=0.

If U is continuous, for v∈F define j(v)=P_{1⊥}B^Tv. If j(v)=0, then B^Tv=t1. Pairing with d gives t=0 since 1·d>0. But B^Tv=0 implies v^TD=0, hence v=0. Thus j embeds F in the fixed space 1⊥⊂R^k.

If V is continuous, d is continuous and v↦P_{1⊥}P_{d⊥}VA v is an embedding. Indeed P_{1⊥}|_{d⊥} is an isomorphism because d·1>0. If the displayed map vanishes, VA v is a multiple of d, so Dv=0 and v=0. The upper construction (2) is already strictly positive. No globally continuous row normalization is needed, and zero individual row sums cause no loophole. The same argument applies to a normalized approximate product in Proposition3 by using invertibility of its compressed D′ instead of D=βP_F. An unnormalized approximate product requires the separate, slightly smaller-radius estimate in Proposition3b below.

**Exact real-factor comparison.** Let G=ε¹⊕E be the full row bundle, realized concretely as span(c,E)⊂X×R^m. The minimum continuous real factor size is g(G). A continuous readout factor restricts injectively to G because H has no kernel on its row space; a continuous preparation factor projects surjectively to the column bundle, which is isomorphic to G. Conversely, choose an isometric embedding j:G→R^t, t=g(G), and set K=jP_G. Then K^TK=P_G and H=(HK^T)K. Thus the exact positive-minus-real gap in this projection family is

    g(E)+1−g(ε¹⊕E) ∈ {0,1}.

The inequalities g(E)≤g(ε¹⊕E)≤g(E)+1 follow by restriction and adjoining a trivial coordinate. The unbounded projective gap is pointwise-versus-global, not positive-versus-real. The two-sphere example attains the possible one-state normalized-versus-unconstrained-real gap. Signed row-stochastic factors satisfy the same lower bound as nonnegative stochastic factors; the proof uses the affine hyperplane, not the signs of normalized coefficients.

The minimum s is an independently defined topological invariant of the observed bundle, not an algorithmic claim that its value is always easy to compute. The following families have explicit certificates.

## 4. Projective-space family: an unbounded local/global gap

Take X=RP^d, m=d+2, and the tautological line E_[u]=R u⊂W for u∈S(W), u identified with −u. Formula (1) becomes

    H_0([u])=c,
    H_i([u])=c+β(a_i·u)u.                                (4)

Only the projection uu^T occurs, so there is no chosen global sign. H is real analytic as a function of the projective parameter.

The tautological line over RP^d has g(E)=d+1. For d≥1, if E embeds in a trivial rank-s bundle, its orthogonal complement has total Stiefel–Whitney class

    w(E⊥)=(1+a)^(−1)=1+a+⋯+a^d,

where a=w_1(E) and a^d≠0. The complement has rank s−1, so s−1≥d and s≥d+1. The supplied embedding in W realizes equality. Equivalently, an embedding would give a nonvanishing odd map S^d→R^s, and Borsuk–Ulam gives s≥d+1.

Consequently H has pointwise rank and nonnegative rank 2, but continuous stochastic factor size exactly d+2. For d=0, the base is one point and ordinary rank gives size 2. For d=2, pointwise size 2 becomes global size 4, certified by a²≠0.

**Important classical subtraction.** The full row bundle is ε¹⊕E. For this particular projective family, its minimum trivial-bundle embedding dimension is also d+2. Therefore the very same exact obstruction holds for arbitrary continuous real matrix factors, without stochasticity. Swan's classical example already computes this generator number. The projective gap is not a new positivity obstruction.

### A concrete circle

For d=1, m=3, take

    a_1=(1,−1,0)/√2,
    a_2=(1,1,−2)/√6,
    u(θ)=cos θ a_1+sin θ a_2,       θ modulo π.

Then H has three rows:

    c,
    c+β cos θ u(θ),
    c+β sin θ u(θ).

Every entry is strictly positive for β<1/6. At each θ a two-state factorization has emissions c±δu(θ), with preparation weights (1±(β/δ)cos θ)/2 and (1±(β/δ)sin θ)/2. After θ increases by π the two emission states exchange. The observed H returns to itself. No globally continuous two-label choice exists, while three global states suffice. The statement is about label compatibility around the loop, not a visible outcome called “global sign.”

## 5. An unconstrained-real versus normalized comparison: the two-sphere

Let X=S²⊂R³, take m=4,n=3, and identify R³ isometrically with W by A. Let

    E_x=A(x⊥)=T_xS²,        P_x=A(I−xx^T)A^T.

Use (1), with 0<β<1/12. Every table has ordinary rank and pointwise nonnegative rank 3.

The tangent bundle TS² is nontrivial and cannot embed in a trivial rank-2 bundle: a fiberwise injective map between bundles of equal rank would trivialize it, contradicting the hairy-ball theorem. It embeds in a trivial rank-3 bundle by its standard realization in R³. Hence g(TS²)=3 and Theorem 2 gives continuous stochastic factor size exactly 4.

In contrast, the full row bundle ε¹⊕TS² is trivial of rank 3. There is an explicit continuous real factorization of size 3. Put e_0=1_4/2, a unit vector normal to W, and define F_x:R³→R⁴ by

    F_x(v)=(v·x)e_0+A(v−(v·x)x).

F_x is an isometry onto span(c,E_x). Since every row of H lies in that image,

    H=(H F_x) F_x^T.                                     (5)

These are globally continuous real factors of inner dimension 3. Rank prohibits smaller real factors. Thus:

    pointwise nonnegative size = 3,
    continuous real size = 3,
    continuous stochastic size = continuous nonnegative size = 4.

This contrast survives subtraction of the projective example's ordinary linear obstruction. The extra normalized state is tied to the centered bundle after affine normalization, whereas arbitrary real factorization can use the stabilizing normal direction. In (5), the readout factor satisfies F_x^T1_4=2x, which varies with x. It is not a signed stochastic factor with a fixed normalizing vector. Both-factor continuous nonnegative realizations obey the same lower bound, including factorizations with vanishing row sums. It remains to audit this exact stochastic/affine formulation against the classical theory of affine bundles and normalized realizations before asserting novelty.

**A temporal interpretation needs another theorem.** Local enclosing 3-simplices can rotate continuously with the tangent planes. Their transition matrices need not be permutations, while isomorphisms of finite stochastic simplices are permutations. Pointwise or local stochastic factorizations do not thereby form one compatible finite-state stochastic bundle. The dynamic construction in the next section uses the special rank-one sign cover and does not establish such a lift for TS². The separately constructed contraction family in Section12 addresses this issue without claiming that rotated local triangles glue by permutation isomorphisms.

## 6. A separate all-horizon native construction for the sign family

Use the projective parameter [u]∈RP^d, m=d+2, and choose constants 0<α<1, 0<δ<1/m, with β=αδ (and β<1/(mn) if Theorem 2's general bound is being used). The globally fixed output alphabet is Y={1,…,m}. On the local two-state carrier {+,−}, define emission distributions

    e_±(u)=c±δu.

The hidden sign labels exchange under u↦−u; the public output labels y do not.

Let S exchange the two signs and J=11^T/2. The controlled output/next-state matrices are

    M_y^hold(u)=diag(e_+(u)_y,e_−(u)_y),
    M_y^flip(u)=S diag(e_+(u)_y,e_−(u)_y),
    M_y^refresh(u)=J diag(e_+(u)_y,e_−(u)_y).              (6)

The action is performed before emission. Every action's outcome sum is stochastic. For every fixed global outcome y and action a,

    M_y^a(−u)=S M_y^a(u) S.                              (7)

Preparations are π_0=(1/2,1/2) and

    π_i(u)=((1+α a_i·u)/2,(1−α a_i·u)/2).

They satisfy π_i(−u)=π_i(u)S. The complete controlled response law

    π_i(u) M_{y_1}^{a_1}(u)⋯M_{y_t}^{a_t}(u)1

therefore descends to RP^d. Its single-hold table is exactly (4). There is genuine state reuse: under π_0, two consecutive holds have centered output covariance δ²uu^T; a flip before the second output changes its sign, while refresh removes it. No clock or unbounded history state is introduced. Refresh changes the hidden transition mechanism from persistence to independent resampling, rather than only relabeling public output.

### Explicit global d+2-state lift

Let 0<η<1/√(m(m−1)). Every unit u∈W has both max_j u_j>η and min_j u_j<−η. Indeed sum u_j=0 and ||u||=1 imply max u_j≥1/√(m(m−1)), and similarly for −u.

Define

    q_j^+(u)=(u_j−η)_+ / Σ_l(u_l−η)_+,
    q_j^−(u)=q_j^+(−u),
    h_j(u)=clip(u_j/η,−1,1),
    L_u(j,±)=(1±h_j(u))/2,
    Q_u(±,j)=q_j^±(u).                                  (8)

Q and L are row stochastic, and

    Q_u L_u=I_2.                                        (9)

This holds because q^+ is supported where h_j=1, and q^− where h_j=−1. Also L_{−u}=L_uS and Q_{−u}=SQ_u.

For each public action/outcome define the m×m global kernel and preparation

    X_y^a([u])=L_u M_y^a(u) Q_u,
    ρ_i([u])=π_i(u)Q_u.                                 (10)

All are continuous, nonnegative, normalized, and invariant under u↦−u. The projective parameter stays fixed throughout each word; Q_uL_v need not be identity for different parameters, so this is not a cross-parameter transport theorem. Their exact retention equations are

    X_y^a L_u=L_u M_y^a,
    ρ_i L_u=π_i.                                        (11)

Telescoping QL=I proves equality of all finite controlled response laws, including adaptive choices based on the past public outputs. The comparison is statewise on each local sign chart and agrees under chart changes. It is not merely equality of the initial trace distribution.

This proves an exact global continuous d+2-state upper bound for the entire controlled family, matched by the one-read lower bound. Local two-state models are minimal by the rank-2 table. The construction also covers any other bounded finite action family of outcome-indexed two-state kernels satisfying the fixed-output equivariance (7).

**Smoothness.** The formulas (8) are piecewise smooth and continuous. A C∞ lift is obtained by replacing (t−η)_+ with a smooth function φ(t) that is zero for t≤η and positive for t>η, and replacing clip(t/η,−1,1) by a smooth odd function equal to sign(t) for |t|≥η. The support argument and QL=I are unchanged. Thus smoothness need not be sacrificed. This argument does not supply a globally real-analytic temporal lift; no impossibility or existence claim for analytic temporal lifts is made here.

## 7. Uniform robustness, without a rank promise on the fitted family

For the general projection family (1), keep C and A from (3). Then ||C||op=√m, ||A||op=1, and D=βP_F.

**Proposition 3.** Let H′=U′V′ be any pointwise row-stochastic factor family through k states. Suppose either U′ or V′ is continuous and

    sup_x ||H′(x)−H(x)||op < β/√m.                       (12)

Then k≥g(E)+1. No rank, nonnegative-rank, or common-row-space condition is imposed on H′.

**Proof.** D′=CH′A satisfies ||D′−βP_F||op<β. Therefore P_FD′|F is invertible on each fiber.

If V′ is continuous, compose V′^T|1⊥ with projection onto E. The range contains the image of the invertible fiber endomorphism just obtained (after transposing and identifying E with F), and is therefore onto E. If U′ is continuous, project CU′|1⊥ onto F. Since D′=(CU′)V′A, its range also contains the image of the invertible P_FD′|F. In both cases the adjoint embeds E into a trivial rank-(k−1) bundle. ∎

For TS², every continuous three-state stochastic model stays at least β/2 away somewhere in operator norm, whereas (5) is an exact continuous real rank-3 model. This gives a robust comparison genuinely separating normalization from arbitrary real factorization.

**Proposition 3b, nonnormalized and one-channel approximation.** Let H′=UV with V≥0, U arbitrary real, and at least one of U,V continuous. The product need not be stochastic or continuous. If

    sup_x ||H′(x)−H(x)||op < β/m,

then k≥g(E)+1. This is a conservative uniform exclusion radius, not an optimal threshold.

For the U-continuous proof, put D_U=CU and use J(e)=P_{1⊥}D_U^TA^Te for e∈E. If J(e)=0, then D_U^TA^Te=t1, so (CH′)^TA^Te=tV^T1 lies in the positive or negative orthant. But (CH)^TA^Te=βe. For every e⊥1, the distance to either orthant is at least ||e||/√m: the positive and negative parts have equal ℓ¹ norm, and each has support at most m−1. Since ||C||op=√m, the displayed approximation radius makes this impossible for nonzero e. Thus J embeds E in fixed 1⊥.

For the V-continuous proof, let d=V1. It is nowhere zero: otherwise V=0 and ||H′−H||op=||H||op≥1 at that point. Use J(e)=P_{1⊥}P_{d⊥}Ve. Its kernel implies Ve=t d. Some row of V has positive sum, so t is a convex average of coordinates of e and |t|≤√((m−1)/m)||e||. Consequently ||e−t1||≤√m||e||. Now CH′(e−t1)=0, whereas CH(e−t1)=βA^Te. Hence β||e||≤√m||H′−H||op√m||e||, a contradiction. This direct argument avoids any unjustified continuous normalization at zero rows. It was independently checked against the companion static review `affine_independent.md`.

For RP^d, a positive uniform gap also follows without stochasticity or positivity from the minimum nonzero singular value of H and the classical full-row-bundle obstruction. With m=d+2, its uniform minimum nonzero singular value is

    σ_*²=[1+β²−√((1+β²)²−4β²/m)]/2.

In particular σ_*≥β/√(m(1+β²)). A real approximant with op error <σ_* cannot factor continuously through fewer than g(ε¹⊕E) states: a continuous readout must restrict injectively to the target row bundle, or a continuous preparation factor must surject onto the target column bundle after projection. This is the usual stable bundle obstruction, not an intrinsically probabilistic surprise.

## 8. Finite evidence: what is and is not certified

No finite sample of parameter locations alone rules out a global continuous two-state fit of the projective family. To see this, choose disjoint neighborhoods of the finitely many distinct sampled parameters. On each neighborhood choose a local sign and its exact two-state factors. Use a continuous cutoff supported in that neighborhood and equal to one at the sample. Interpolate each stochastic factor separately to one fixed default stochastic factor outside those neighborhoods. Convex interpolation preserves stochasticity. The resulting globally continuous two-state factors match every sampled H exactly but need not stay near H between samples. They must deviate somewhere by Proposition 3.

A finite-net certificate needs a quantitative regularity promise. Let {x_l} be an h-net in a fixed metric on X. Suppose truth H and candidate H′ have known operator-norm moduli ω and ω′, respectively, and the measured table error at each x_l is at most e. Then

    sup_x ||H′(x)−H(x)||op ≤ e+ω(h)+ω′(h).

If this is less than β/√m, Proposition 3 excludes k<g(E)+1. Sampling error can be included in e using the declared repeated-trial model. A modulus of the truth alone does not bound an unconstrained candidate between sample locations. The topological parameter family, its coverage, and those candidate regularity assumptions must remain visible.

The companion `topology_finite.md` sharpens these statements. Deterministic finite adaptive transcripts admit even analytic factor interpolants. For smooth alternatives over RP^d, a random narrow seam yields a single fixed global two-state alternative arbitrarily close in transcript total variation to the target for any adaptive randomized algorithm that stops almost surely after finitely many target queries. The alternative can retain centered rank one everywhere. A common quantitative modulus is essential; smoothness alone is insufficient. The seam alternatives can even maintain a uniform nonzero centered singular-value bound β/2 independent of seam width, since their interpolated vector has squared norm at least 1/2. A spectral-gap promise alone does not fix the empirical obstruction.

The randomized statement does **not** extend by this argument to analytic alternatives under an exact-real oracle. When the target analytic table is known, any fixed distinct analytic alternative differs outside a measure-zero zero set, so a random exact equality query distinguishes it almost surely. Deterministic analytic interpolation and randomized smooth impossibility are distinct claims. The companion gives full constructions, quantifiers, temporal extensions, and the finite spectral-cocycle certificate with its prior-art comparison.

## 9. Source and novelty ledger

- **Swan, “Vector Bundles and Projective Modules,” 1962, Example 2 (Chase), pp. 270–271, and Theorem 4.** The projective-space example already proves that γ¹⊕ε^{k−1} over RP^n needs at least n+k global generators. With k=2 this is exactly the d+2 real-factor obstruction above. The projective number and its characteristic-class proof are therefore emphatically not new. [Official DOI](https://doi.org/10.1090/S0002-9947-1962-0143225-6).
- **Hazewinkel, “Moduli and Canonical Forms for Linear Dynamical Systems II: The Topological Case,” 1977.** Its continuous-canonical-form obstruction and universal state bundle directly precede the local/global interpretation. [Primary institutional PDF](https://ir.cwi.nl/pub/10022/10022D.pdf). Hazewinkel's 1979 account, §5.2, Theorem 5.2.2, treats constant-degree response families and bundle-valued minimal realization; global minimal matrix realization depends on triviality. [Primary PDF](https://ir.cwi.nl/pub/10385/10385D.pdf). A new label for this phenomenon would not be a contribution.
- **Grasse, “A vector-bundle version of a theorem of V. Doležal,” 2004.** The range/kernel bundle of a continuous constant-rank matrix and its continuous frames are direct matrix-factorization controls. [DOI](https://doi.org/10.1016/j.laa.2004.05.014).
- **Shitov, “A universality theorem for nonnegative matrix factorizations,” 2016/2018.** Fixed-matrix factorization spaces can have arbitrary bounded semialgebraic complexity, modulo the specified equivalence. This is a warning against generic canonical-factor or selection claims, not an established proof of the present normalized-family formula. [Primary paper](https://arxiv.org/abs/1606.09068).

- **Mond–Smith–van Straten, “Stochastic Factorizations, Sandwiched Simplices and the Topology of the Space of Explanations,” 2003.** Full primary text inspected. Theorem2.4 identifies rank-size factorization spaces with ordered sandwiched simplices. Proposition3.1 describes the rank-2 fiber as two rectangles before permutation quotient. Lemma3.2 and Theorem1.1 connect the small-matrix fiber to regular simplices and orthogonal frames. This is a close antecedent for the rank-sized label/frame obstruction; the inspected statement does not give the g(E)+1 family optimum over nonminimal latent sizes. [Author-hosted PDF](https://download.uni-mainz.de/mathematik/Algebraische%20Geometrie/DvS-Publikationen/30.Stochastic%20factorizations%2C%20sandwiched%20simplices%20and%20the%20topology%20of%20the%20space%20of%20explanations%20-%202003.pdf).
- **Hrubeš, “On ε-sensitive monotone computations,” 2020, Lemma3.9.** Adding a sufficiently large positive rank-one background to any rank-r matrix gives nonnegative rank at most r+1. Thus the pointwise small-signal positive construction itself has a direct predecessor; it is not the potential residual. [Primary PDF](https://users.math.cas.cz/~hrubes/PDFs/Epsilon.pdf).
- **Ke–Montiel Olea–Nesbit, “Robust machine learning algorithms for text analysis,” 2024, Supplement AppendixA.** The appendix studies continuity of the set-valued exact stochastic NMF correspondence and associated extremal values under its hypotheses. This is not a theorem supplying one globally continuous factor selection over a nontrivial parameter family. No contradiction with the bundle obstruction is inferred. [Primary supplement](https://joseluismontielolea.com/OnlineAppendix_LDA_2024.pdf).
- **Gubeladze, “Affine-compact functors,” §8.** Sandwiching and complementing functors generalize the fixed-polytope spaces associated with stochastic factors; their topology and extension problems are already studied. This is a comparison control, not a located proof of the resource formula here. [Primary paper](https://arxiv.org/pdf/1608.04177).

- **Anderson, “The Realization Problem for Hidden Markov Models,” 1999.** The primary institutional abstract explicitly treats reconstruction from all finite-word probabilities through Hankel matrices and polyhedral cones. This is a strong predecessor for the temporal realization problem, not a parameter-bundle minimum-width theorem inspected here. [DOI](https://doi.org/10.1007/PL00009846), [institutional abstract](https://researchportalplus.anu.edu.au/en/publications/realization-problem-for-hidden-markov-models/).
- **Vidyasagar, “The Complete Realization Problem for Hidden Markov Models: A Survey and Some New Results,” inspected 2009 manuscript.** Theorem6.1 states the stable-polyhedral-set realization criterion; the proof of Theorem9.2 constructs nonnegative matrices through D(u)Y=YG(u) and transfers all-word probabilities. Thus finite-cone generation and the basic intertwining lift are classical. The inspected results concern a process and its invariant cone, rather than optimal continuous generator counts over an external parameter bundle. [Primary manuscript](https://personal.utdallas.edu/~mxv091000/Research/hmm-full.pdf#page=1); the direct URL sometimes redirects, but the indexed PDF was inspected. [Accessible 2005 conference precursor](https://skoge.folk.ntnu.no/prost/proceedings/cdc-ecc05/pdffiles/papers/0862.pdf).

- **Monràs–Winter, “Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem.”** Definition5 fixes terminal vector (1,…,1) in the positive native model; Theorem6 supplies the invariant polyhedral-cone criterion; Section4 gives quotient/minimal realization comparisons. This is an exact native-semantics predecessor, not a located parameter-bundle width theorem. [Primary text](https://arxiv.org/html/1412.3634).

The residual worth auditing is the exact stochastic/affine resource formula for projection families, its stable-normalization contrast on TS², and the explicit parameter-dependent temporal constructions with their statewise equations. These may still reduce to standard normalized realization or affine-bundle arguments. Search failure is not novelty evidence. No claim of a new general theory of observational emergence is supported yet.

## 10. Next attacks and stopping tests

1. Check the normalized formula against projective-module generator theory with a distinguished order unit, affine bundle factorizations, and positive realization over C(X). If the complete theorem is a standard corollary, retain it as a sharp benchmark rather than promote it.
2. Audit Section12 against parameter-dependent positive realization with a distinguished terminal functional. It supplies a temporal TS² normalization gap by an explicit contracting model, not by gluing rotating simplices. Seek a sharper input-level theorem beyond this deliberately small invariant neighborhood, without assuming the unknown native cone.
3. Replace known parameter topology by an independently verifiable finite certificate: a response-family presentation plus a uniform gap and a valid modulus, or a certified bundle cocycle. Merely plotting sample eigenvectors does not qualify.
4. Test changes of evidence. A fiberwise-injective observation map preserves the bundle obstruction; restricting to a trivializing chart can remove it; deleting tests can create rank drops. State each comparison at the correctly restricted parameter base and experiment family.

The immediate positive result is a concrete, auditable law linking an observation-derived centered bundle to continuously normalized latent resources. Its mathematical content and its source-level novelty are separate questions.

## 11. Reproducible numerical regressions

`topological_native_checks.py` and `topological_native_checks_results.json` check 105 projective parameters in dimensions d=0,…,6 and 100 tangent-sphere parameters. They verify row normalization, positivity, local/global factorizations, antipodal descent, QL=I, statewise retention, six-step controlled word laws, hold/flip/refresh covariance signatures, the sphere's real three-factor and positive four-factor formulas, and the circle seam's state swap. Maximum reported residual is below 5×10^−16. These floating-point tests supplement the displayed algebra; they do not prove the topological lower bounds, certify exact arithmetic, or establish novelty.

## 12. A stronger temporal construction for general observable bundles

**Algebra and numerical regressions independently checked; no novelty clearance.** This construction addresses the temporal gap stated in Section5. It does not glue local simplices using rotations. Instead it constructs one global larger native model and actual stochastic comparison maps from independently chosen smaller local realizations.

Keep E⊂X×W, W=1⊥R^m, n=m−1, and 1≤r=rank E≤s=g(E)≤n. Fix

    ε=1/(4m),   γ=τ=1/(16n²),   Λ=1/(16n).

Supply a finite action set with continuous sections t_a∈E, ||t_a||≤τ, and constants or continuous functions |λ_a|≤Λ. For example, use a hold action t=0,λ=Λ; a refresh action t=0,λ=0; and kicks t=±τP_Ea_i with λ=Λ. All quantities in this specification are given directly by the projection family, not an unknown positive factorization.

In this section an action chooses the transition law used **after** the current output is emitted. In particular λ=0 refresh first emits from the old state and then resets to t_a. This timing differs from Section6, where flip/refresh occur before emission; the two interfaces are not identified.

Define a finite linear response presentation on G=ε¹⊕E. An unnormalized state is (q,z), with terminal evaluation q. For each globally fixed output y∈{1,…,m}, let

    T_{a,y}(q,z)=(q/m+εz_y, (q/m+εz_y)t_a+λ_a z/m).       (13)

This is linear in (q,z). Its outcome sum is

    Σ_y T_{a,y}(q,z)=(q,qt_a+λ_a z).

The initial preparations are (1,0) and (1,γP_Ea_i). Repeated application and final evaluation define all finite controlled response laws. Their positivity is not assumed: the following native construction proves it.

### Theorem 4: exact temporal resource formula

The response family (13) has pointwise minimum stochastic state size r+1, globally continuous stochastic/nonnegative state size g(E)+1, and globally continuous unconstrained real linear state size g(ε¹⊕E). The real comparison allows a continuous parameter-dependent terminal covector; it is not a quasi-stochastic model with a fixed terminal vector. In the nonnegative weighted variant, initial weights, outcome-transition matrices, and terminal evaluation are all nonnegative; otherwise the first-read factorization need not be nonnegative and this lower bound is not claimed. Ordinary stochastic models use normalized initial weights and terminal vector 1. These statements require only the finite family of preparations and the fixed public action/outcome vocabulary above. The external parameter x is fixed within each word. Changing x between steps requires a separate transport law and is not covered by the local-to-global intertwiner. They hold for all finite horizons and adaptive public protocols.

The native systems can be chosen with strictly positive outcome/next-state matrix entries. No unused clock coordinate or growing history state is needed. Local minimal native systems compare to a global optimal native system through explicit stochastic statewise maps. Local systems are not claimed to be isomorphic by permutations on overlaps.

### Global native construction

Choose an isometric embedding j:E→R^s and the unit regular simplex ζ_1,…,ζ_{s+1}⊂R^s. Its projected vertices are

    v_i=j*ζ_i∈E,       ||v_i||≤1.

For w∈E define affine barycentric functions

    b_i(w)=(1+s ζ_i·jw)/(s+1).

They sum to one and reconstruct w: Σ_i b_i(w)v_i=w. If ||w||<1/s, every b_i(w)>0.

For a normalized state z define

    e_y(z)=1/m+εz_y,
    F_{a,y}(z)=t_a+λ_a z/[m e_y(z)].                       (14)

On ||z||≤1, e_y(z)≥3/(4m), and

    ||F_{a,y}(z)|| ≤ 1/(16n²)+1/(12n)
                    ≤ 7/(48n) < 1/s.

Thus the following are strictly positive native controlled kernels on s+1 fixed labels:

    N_{a,y}(i,j)=e_y(v_i)b_j(F_{a,y}(v_i)).                (15)

For each i, summing over j gives e_y(v_i), and summing over y gives one. Preparation probabilities are b_j(0) and b_j(γP_Ea_i), also strictly positive.

Let R map a native distribution to its mass and first moment, R(ρ)=(Σ_iρ_i,Σ_iρ_i v_i). Equations(14)–(15) give

    R(ρ N_{a,y})=T_{a,y}(R(ρ)).                           (16)

This proves positivity and exact equality for arbitrary finite words. Adaptive protocols are sums over the corresponding public outcome branches, so the same equality holds for them.

### Pointwise/local smaller realization

On a trivializing chart for E, choose an orthonormal frame and a regular r-simplex of radius

    R_loc=1/(2n).

Its affine barycentric functions are nonnegative on the ball of radius R_loc/r. For ||z||≤R_loc,

    e_y(z) ≥ (1−1/(8n))/m ≥ 7/(8m),
    ||F_{a,y}(z)|| ≤ 1/(16n²)+1/(28n²)
                   =11/(112n²) < R_loc/r.

The same formula(15), with the local simplex and its barycentrics, therefore defines an r+1-state strictly positive native model. The preparations lie inside its inball because γ< R_loc/r. This constructs local native kernels directly; it does not assume their existence.

The first public output table is (1) with β=εγ. Its rank is r+1, so fewer states are impossible pointwise.

### Actual stochastic local-to-global comparison

Every local vertex w_i has norm R_loc≤1/(2n)<1/s and hence lies inside the global projected simplex. Define

    L_ij=b_j(w_i).

This is a strictly positive stochastic map from local states to global states, and it preserves their observable first moments. It satisfies the stronger statewise equations

    N_local,a,y L=L N_global,a,y,
    ρ_local,i L=ρ_global,i.                              (17)

To verify this, note that b is affine and

    e_y(z)b_j(F_{a,y}(z))
      = e_y(z)b_j(t_a)
        + (λ_a/m) times the linear part of b_j evaluated at z

is affine in z. Taking its barycentric expectation over either simplex gives the same value at w_i. This proves(17) for every fixed action and outcome, not merely after summing outcomes or under the designated initial preparation.

There is no assertion of a reverse statewise map. The large global simplex need not lie inside a particular small local one. Different local constructions compare through their common global native target, rather than by illicitly treating a rotation as a stochastic isomorphism.

### Global optimality and real comparison

The first-read table is the projection family with β=εγ. Therefore any globally continuous native model has at least g(E)+1 states by Theorem2, whereas(15) attains that bound.

A real linear realization on a fixed carrier is obtained by isometrically embedding G into a trivial bundle of rank g(G), conjugating(13) into that bundle, and extending by zero on its orthogonal complement. Initial states and final evaluation are transported along the same embedding. The first-read table forces at least g(G) real states. Thus the exact unconstrained real minimum is g(G). The transported terminal covector is generally parameter-dependent.

**Fixed-terminal signed comparison.** If the real model is instead required to have one fixed nonzero terminal covector t on R^k and normalized preparations p_i t=1, then its exact minimum is g(E)+1, even allowing signed kernels and initial weights. For the first-read factorization, U has rows p_i and V has columns M_y t. Every preparation difference lies in the fixed ker(t). The continuous readout map V^T restricted to ker(t), projected onto E, is onto E, so E embeds in a fixed rank-(k−1) space. Equivalently the preparation-side proof uses CU t=0. The positive model already attains the resulting lower bound.

For TS², a minimal real three-dimensional bundle trivialization turns terminal evaluation into a multiple of x, not a constant vector. One cannot make it constant by a globally continuous change of coordinates: its kernel is TS². Consequently the 3-versus-4 comparison is a normalization/terminal-structure gap. Positivity is sufficient to impose it, but is not necessary.

For E=TS² this yields a full controlled family with pointwise native size3, global unconstrained real size3 with a varying terminal covector, and global normalized native size4 (whether signed or positive). The global-minus-pointwise projective gap also persists for E=γ¹ over RP^d.

### Genuine memory and interventions

Under the outcome-summed dynamics, z evolves as z↦t_a+λ_a z. A hold with λ_a≠0 retains distinctions for arbitrarily many successive nonterminal transitions, even though they contract. A refresh λ_a=0 removes those distinctions, which affects later output laws. Kicks can alter them in different projected directions. Two kicks generally do not commute: their two-step affine translations differ by (1−λ)(t_b−t_a). These are interventions on a transition mechanism with the public readout held fixed.

This is a deliberately strongly contracting family; it does not establish arbitrary stochastic assembly, arbitrary invariant-cone synthesis, or the whole multistage flagship. Its residual content is an exact bundle-sensitive positive resource law with real temporal use and typed native comparisons. Classical positive realization and polyhedral invariant-cone results remain direct controls.

The temporal regression script `topological_temporal_checks.py` checks 100 tangent-sphere parameters, strictly positive local/global transition entries, preparation and statewise stochastic comparisons, real three-dimensional intertwining, seven-step controlled laws, and the first-read rank-3 table. All checks passed; the largest residual was below 3×10^−16 and the smallest tested native entry exceeded 0.049. These numerical checks are neither topology proofs nor novelty evidence.
