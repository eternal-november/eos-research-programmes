# Finite observation certificates for response bundles

**Supplement snapshot:** contextual research material, not exact-hash-certified against the final circle review. The final report in the package root takes precedence. See ../SOURCE_STATUS.md.

**Research note, 3 November 2026.** Derived for the accompanying `topological_native_seed.md`. The results below are elementary combinations of established spectral perturbation, bundle cocycles, and normalized factorization. They are not claimed novel. In particular, finite noisy bundle reconstruction and characteristic-class algorithms are already explicit in Scoccola–Perea. The useful addition here is an end-to-end, checkable interface from sampled stochastic response tables to a normalized latent-state lower bound, together with precise deterministic and randomized limitations.

## Executive findings

1. A known continuum formula for the response is unnecessary. A finite triangulation, measured tables, certified noise and a known response modulus suffice to compute an exact orientation cocycle of a separated *spectral* response bundle. Exact constant rank is unnecessary.
2. For rank one, a finite simplicial cup-product witness can certify an arbitrarily large global state lower bound: if the measured cocycle `a` has `<a^d,z>=1` on a finite d-cycle, every sufficiently close globally continuously normalized realization needs at least `d+2` states.
3. A useful alternative constructs a reference response by barycentric interpolation of the observations. A quantitative modulus on the *candidate* alone can then suffice to rule out that candidate class. A truth modulus is needed to identify the true continuum bundle, not to reject bounded-modulus interpolants.
4. No finite exact transcript rules out unconstrained continuous candidates. This survives deterministic adaptive sampling, even if the candidates must be real analytic. For the projective family, an additional construction proves a uniform randomized impossibility for smooth candidates, including candidates of constant centered rank one. Do not conflate these two regularity statements.
5. Temporal action experiments at a fixed parameter do not remove the obstruction to finite identification: the indistinguishable alternatives can match **every controlled horizon** at every queried parameter. Experiments which change the parameter while transporting a hidden state require extra mechanism and constitute a different oracle.

## 1. Observation and geometry assumptions

Let X be the geometric realization of a supplied finite simplicial complex K, with a supplied metric. Every simplex has diameter at most h. Vertices and their parameter locations are known. The open vertex stars form a finite good cover, with nerve K. In particular, x in the star of v implies d(x,v)<=h. The metric and triangulation are assumptions about the experimental control domain, not conclusions from table samples.

There are p>=2 fixed preparations and m>=2 fixed output labels. H(x) is a p-by-m row-stochastic table, unknown away from the queried vertices. Measurements give row-stochastic tables Hhat_v and a certified simultaneous error bound

    ||Hhat_v-H(v)||op <= epsilon.

Empirical multinomial frequency rows have the required normalization automatically. Define

    C = [-1_(p-1)  I_(p-1)],  ||C||op = sqrt(p),
    B(x)=C H(x),  B_v=C Hhat_v,  G_v=B_v^T B_v.

Thus B1_m=0. Fix a proposed spectral rank 1<=r<=min(p-1,m-1). Let

    gamma_v=lambda_r(G_v)-lambda_(r+1)(G_v).

All eigenvalues are in decreasing order. Internal multiplicities among the first r eigenvalues are harmless. Only separation of this group from the remainder matters. When small residual modes are present, this spectral bundle depends on the specified observable Euclidean metric and the separated spectral group; it is not automatically invariant under arbitrary coordinate changes. At exact rank r it reduces to the ordinary response-span bundle. Finite noisy observations generally cannot certify exact algebraic rank without an additional promise, which is why the spectral formulation is used. Q_v is any m-by-r orthonormal frame for the first r eigenspace, and P_v=Q_v Q_v^T. Numerical implementations must use certified intervals or explicit roundoff bounds for every strict inequality and determinant sign below. A floating-point eigenvector plot is not a certificate. With rational frequency tables, the covariance matrices are rational and the required spectral subspaces can be represented by algebraic data. Positive gap and overlap margins make certified refinement or exact algebraic sign computation terminate; no access to exact continuum probabilities is required for the positive certificate.

A known operator-norm modulus omega satisfies

    ||H(x)-H(y)||op <= omega(d(x,y)).

The following conservative local numbers are fully computable:

    xi = sqrt(p) [epsilon+omega(h)],
    q_v = (2||B_v||op+xi) xi.

For every x in star(v), ||B(x)-B_v||<=xi and ||B(x)^T B(x)-G_v||<=q_v. Throughout the theorem, q_v may instead be any sharper independently certified bound on this last covariance difference, for example one derived from a direct modulus omega_G for B^T B. With centered sampling error epsilon_B=sqrt(p)epsilon, the alternative bound q_v=omega_G(h)+(2||B_v||+epsilon_B)epsilon_B includes both spatial variation and measurement noise.

## 2. Explicit finite orientation-cocycle theorem

**Theorem A.** Assume, at every vertex,

    q_v < gamma_v/4.                                      (A1)

Then the top-r right singular subspaces E_x of B(x) form a continuous rank-r vector bundle E contained in X times 1_m-perp. The data determine a cocycle

    a(vw)=0 if det(Q_v^T Q_w)>0,
    a(vw)=1 if det(Q_v^T Q_w)<0,                            (A2)

on the edges of K. Every determinant is nonzero. This is an exact Z/2-valued simplicial cocycle, and its cohomology class is w_1(E). In particular, a closed edge cycle with odd sum of a is a finite witness that E is nonorientable.

### Proof, including constants

First use the following elementary spectral perturbation bound. For symmetric A and A+R with ||R||=e<gamma/2, where gamma=lambda_r(A)-lambda_(r+1)(A), their top-r projectors satisfy

    ||P(A+R)-P(A)|| <= e/(gamma-e).                         (A3)

For completeness: let U span the top-r space of A and V the complementary spectral space of A+R. Writing A U=U Lambda and V^T(A+R)=M V^T gives a Sylvester equation for V^T U. The spectra of Lambda and M are ordered with separation at least gamma-e. Its integral solution, after a scalar shift separating the two spectra, bounds ||V^T U|| by e/(gamma-e). Equal-rank projector distance equals this largest principal-angle sine. Weyl's inequality gives the required separation. This is a standard Davis–Kahan argument, reproduced to specify the constant.

By (A1), the actual spectral gap is at least gamma_v-2q_v>0, and

    ||P(x)-P_v|| <= q_v/(gamma_v-q_v) < 1/3                (A4)

on star(v). Moreover lambda_r(B(x)^T B(x))>=lambda_r(G_v)-q_v>0. Hence E is well defined and continuous, even if the smaller singular values appear, disappear, or cross one another.

On each vertex star, an actual orthonormal frame is

    F_v(x)=P(x)Q_v [Q_v^T P(x)Q_v]^(-1/2).

The inverse square root exists because (A4)<1. At x in star(v) intersection star(w),

    ||P_v-P_w|| < 2/3,
    sigma_min(Q_v^T Q_w) > sqrt(1-4/9)=sqrt(5)/3.

The actual frame transition F_v(x)^T F_w(x) has determinant with the same sign as Q_v^T P(x)Q_w, since the two normalizing matrices are positive definite. Also

    ||Q_v^T P(x)Q_w-Q_v^T Q_w|| < 1/3.

The whole straight segment between these last two matrices is invertible, since 1/3<sqrt(5)/3. Their determinant signs therefore agree. Thus (A2) is exactly the determinant sign of the genuine transition function on each overlap. On triple overlaps transition functions multiply to the identity, so edge signs satisfy the cocycle condition. Changing Q_v to Q_v R_v changes a by the coboundary of the vertex orientation signs det R_v. The resulting cohomology class is precisely w_1(E). The good-cover identification is the ordinary simplicial/Čech identification for open vertex stars. QED.

A looser presentation saying only that neighboring eigenvectors look close misses both the nonzero-determinant and triangle-consistency steps. The proof above supplies both.

## 3. From the certified bundle to normalized latent resources

Write g(E) for the smallest s such that E embeds in a trivial real rank-s bundle. Let F denote the top-r *left* singular bundle of B. Since the first r singular values are positive, B:E->F is a bundle isomorphism. Define a certified positive signal bound

    s = min_v sqrt(lambda_r(G_v)-q_v) > 0.                 (B1)

This bounds sigma_r(B(x)) from below over all X.

**Theorem B, spectral normalized-factor obstruction.** Suppose H'=U'V' is row stochastic through k states, and either U' or V' is continuous. There is no rank promise on H'. If

    sup_x ||C(H'(x)-H(x))||op < s,                         (B2)

then k>=g(E)+1.

**Proof.** Set B'=C H'. The bundle map P_F B'|E:E->F differs from the invertible B|E by less than its smallest singular value, so it is invertible.

If V' is continuous, the map P_E V'^T restricted to 1_k-perp is a continuous surjection onto E. Indeed its image contains that of P_E B'^T|F, which is invertible, because U'^T C^T maps into 1_k-perp: C U'1_k=C1_p=0.

If U' is continuous, P_F C U' restricted to 1_k-perp surjects onto F. Its image contains P_F B'|E; subtracting a multiple of 1_k from V'e does not change C U'V'e. Taking metric adjoints gives a rank-(k-1) trivial bundle containing E, or the isomorphic F. QED.

If both factors are continuous and nonnegative but not normalized, the same conclusion holds for a row-stochastic product H': normalize by t=B1, putting U=A diag(t). This U is continuous and row stochastic. Normalize each nonzero row of B, and choose an arbitrary probability row where t=0. The resulting V can be discontinuous there, but UV=H' and the preparation-only proof applies. This does not assert the same conclusion when only one unnormalized factor is continuous.

This is an affine normalization obstruction. It does not follow from positivity alone. It is also not restricted to the specially designed projection table in the seed.

### Finite candidate comparison

Assume the candidate has known operator-norm modulus omega' and fits measured vertex tables to tolerance f:

    max_v ||H'(v)-Hhat_v||op <= f.

For a nearest vertex, or any vertex in the simplex of x,

    ||H'(x)-H(x)||op <= f+epsilon+omega(h)+omega'(h).

Consequently the fully finite sufficient rejection condition is

    sqrt(p)[f+epsilon+omega(h)+omega'(h)] < s.              (B3)

Together, (A1), a cohomology witness and (B3) certify a lower bound on k. The candidate modulus may instead be derived from explicit factor moduli. In operator norm, row-stochastic factors give

    omega_H'(h) <= sqrt(k) omega_U'(h)+sqrt(p) omega_V'(h).

Uniform maximum-row l1 norms yield a dimension-friendlier bound via stochastic contraction. A known truth modulus alone does **not** constrain an arbitrary candidate between vertices.

### Finite characteristic-class witness

For arbitrary rank r, an odd orientation cycle proves E nontrivial, hence g(E)>=r+1 and k>=r+2. This need not be the strongest possible lower bound.

For rank one, w(E)=1+a and the formal inverse is 1+a+a^2+... . Fix a total order on vertices. The ordinary simplicial cup product is explicitly

    a^d([v_0,...,v_d]) = product_(j=0)^(d-1) a([v_j,v_(j+1)]) mod 2.

Provide a finite mod-2 d-cycle z (its simplicial boundary is zero) and check

    <a^d,z>=1.                                            (B4)

If E embeds in R^s, its complement has rank s-1 and total Stiefel–Whitney class (1+a)^(-1). A nonzero a^d forces s-1>=d, so

    g(E)>=d+1,     k>=d+2.

No prior declaration that X is RP^d is needed for this implication. The finite cycle and cup evaluation carry the cohomological evidence. However, the triangulated parameter domain or a separately certified model of it remains necessary.

**Important limitation for the seed's S² example:** w_1(TS²)=w_2(TS²)=0. The orientation/cup-power certificate does not detect that tangent bundle's nontriviality. An integer Euler class, equal to 2 on S², or another suitable obstruction is necessary. Scoccola–Perea give an approximate-cocycle Euler-class algorithm for oriented rank two, which is the appropriate existing tool to use here. A zero w_1 result is not evidence of triviality.

### An explicit integer Euler cocycle for rank two

The TS² lower bound can also be certified from finite data, with a stronger margin. Suppose r=2, the observed orientation cocycle is a coboundary, and

    q_v < gamma_v/21 at every vertex.                     (B5)

Then (A3) bounds the projector error on every star by e_0<1/20, where e_0=max_v q_v/(gamma_v-q_v). Solve a(vw)=b(v)+b(w) mod 2 and multiply one column of Q_v by (-1)^b(v). All overlap determinants are now positive. Set

    R_vw = polar(Q_v^T Q_w) in SO(2).

For each oriented edge choose an angle theta_vw with R_vw=rotation(theta_vw), and define theta_wv=-theta_vw, even when a principal angle equals pi. For increasing vertices v<w<z, compute

    n(vwz)=nearest_integer[(theta_vw+theta_wz-theta_vz)/(2 pi)].   (B6)

There is no rounding ambiguity under (B5). The integer cochain n is a genuine cocycle representing the Euler class of E, up to the global orientation/sign convention.

**Proof of the robustness and identification.** Use the actual canonical frames F_v from Theorem A, after the same orientation changes. Principal-angle identities give

    ||F_v(x)-Q_v||F^2
        =2 sum_(j=1)^2 [1-cos(theta_j)]
        <=2 sum_(j=1)^2 sin(theta_j)^2 <=4 e_0^2.

Thus A_vw=Q_v^T Q_w and the actual transition T_vw(x)=F_v(x)^T F_w(x) differ in Frobenius norm by at most 4e_0. The polar factor is the nearest orthogonal matrix to A_vw, so

    ||R_vw-T_vw(x)||F <=8e_0.

For two planar rotations, Frobenius distance is 2 sqrt(2) times the sine of half their angular distance. Therefore their angular distance is at most

    zeta=2 arcsin(2 sqrt(2)e_0) <0.284 radians.

There is consequently a unique continuous lift of T_vw(x) to an angle Theta_vw(x) within zeta of the chosen constant theta_vw on the entire overlap. Choose reverse lifts antisymmetrically. On a triple overlap,

    [Theta_vw(x)+Theta_wz(x)-Theta_vz(x)]/(2 pi)

is an integer, because the true transitions multiply exactly. It is constant on the overlap and differs from the sampled expression in (B6) by less than 3zeta/(2 pi)<1/2. Thus (B6) is exactly the usual integer Čech cocycle of lifted oriented transition functions. Its cocycle property and Euler-class interpretation follow directly. This is the angle-lift construction underlying Scoccola–Perea §6.3, with a separate explicit response-to-transition error estimate here.

An integer simplicial 2-cycle Z with <n,Z>!=0 is sufficient to prove E nontrivial (not necessary when a nonzero Euler class is torsion), so g(E)>=3 and Theorem B gives k>=4. For tangent-plane data on S², a certificate with |<n,[S²]>|=2 is the appropriate witness. Computation of a zero mod-2 Stiefel–Whitney class cannot substitute for this integer calculation. The same construction applies to the data-interpolant bundle if its stronger margin is checked.

This finite certificate supplies the normalized lower bound, not an exact rank-three real upper bound for an otherwise unknown noisy truth. The latter still requires an independent global real realization or an appropriate model-class promise. In the seed it is supplied by the explicit stabilized tangent-bundle factorization.

## 4. A data-only reference alternative

There is a stronger separation between *testing a model class* and *identifying the true bundle*. Define the completely explicit barycentric response

    Hbar(x)=sum_v phi_v(x) Hhat_v,

where phi_v are the standard nonnegative hat functions on K. This table is row stochastic. Set Bbar=C Hbar. For each vertex use the computable star variation

    d_v = max_{w adjacent to v} ||B_w-B_v||op (set d_v=0 at isolated vertices),
    qbar_v=(2||B_v||op+d_v)d_v.

Vertices of every simplex containing v are adjacent to v, so ||Bbar(x)-B_v||<=d_v on star(v). If

    qbar_v<gamma_v/4                                      (C1)

for every vertex, Theorem A's proof gives a spectral bundle Ebar and the same exact orientation cocycle (A2), **without any assumption about a true H**. Set

    sbar=min_v sqrt(lambda_r(G_v)-qbar_v)>0.

Every candidate with vertex fit f and known modulus omega' satisfies

    ||H'(x)-Hbar(x)|| <= sum_v phi_v(x)||H'(x)-Hhat_v||
                       <= omega'(h)+f.

Thus

    sqrt(p)[f+omega'(h)] < sbar                            (C2)

already rules out k<g(Ebar)+1. Neither a known formula nor a modulus for truth is needed for this candidate-class refutation. Noise is accounted for in what fitting tolerance f defines the tested class. If the desired class is required to fit unknown true means to eta, use f=eta+epsilon on the simultaneous confidence event.

To identify Ebar with the *true* E, add the truth conditions (A1). Both true and interpolated projectors then lie within 1/3 of P_v on each star. Hence their mutual distance is <2/3<1 everywhere; projection from one bundle onto the other is a bundle isomorphism. This is a direct, quantitative distinction between a certificate derived from data and a claim about the actual continuum family.

## 5. Sampling, coverage and statistical cost

Suppose there are N vertices, and at every vertex each of p preparations is independently repeated R times with one of m categorical outcomes. No temporal dependence is allowed inside these repeated-trial assumptions unless a different concentration theorem is supplied. Hoeffding plus a union bound gives, with probability at least 1-delta,

    max_v ||Hhat_v-H(v)||op
       <= sqrt( p m log(2 N p m/delta)/(2R) ).              (D1)

This deliberately simple bound uses operator norm <= Frobenius norm and is not minimax optimal. It gives the explicit sufficient repetition count

    R >= [p m/(2 epsilon^2)] log(2 N p m/delta),
    total elementary trials = N p R.

The probability statement calibrates the observations; it does not turn an unverified smoothness assumption into evidence. It is simultaneous over the fixed design. Adaptive designs need appropriately valid confidence bounds, for example a confidence sequence or a union bound over a declared maximum number of stages with allocated failure probabilities.

For Lipschitz truth and candidates, omega(h)=Lh and omega'(h)=L'h. Condition (B3) is

    f+epsilon+(L+L')h < s/sqrt(p).

The spectral condition imposes the additional resolution threshold

    sqrt(p)[epsilon+Lh] < sqrt(||B_v||^2+gamma_v/4)-||B_v||

at each vertex. The constants are conservative. Under controlled D-dimensional geometry, obtaining mesh h generally costs order h^(-D) sites. A bare h-net does not itself supply a triangulation or certify that a guessed nerve has the topology of X.

The scaling with candidate regularity is unavoidable. For the circle projection example, a continuous two-state interpolant exact at all sample points must eventually depart from the truth by the seed's uniform gap Delta=beta/sqrt(m). If the samples have fill radius h and truth/candidate Lipschitz constants are L,L', then

    (L+L')h >= Delta.

Thus fitting denser samples forces L' to grow at least on the order of 1/h. Qualitative continuity, smoothness or analyticity supplies no uniform bound on that growth.

## 6. Deterministic finite-query impossibility, including analytic models

The next two impossibility theorems grant the experimenter an ideal exact-response oracle, which is stronger than finite stochastic trials. Their claims do not assume that a finite number of ordinary trials determines a real probability exactly.

**Theorem C.** Let finitely many distinct locations x_1,...,x_N be queried in a metric space X. Suppose each queried table has some k-state stochastic factorization H(x_i)=U_i V_i. There exist globally continuous row-stochastic factors U,V through k states matching every queried table exactly.

For N>=2 define

    q_i(x)=product_(j != i) d(x,x_j)^2,
    w_i(x)=q_i(x)/sum_l q_l(x).

At x_i, q_i>0 and every other q_l=0. Away from all sample points every q_i>0. Hence the denominator never vanishes, the w_i form a continuous nonnegative partition of unity, and w_i(x_j)=delta_ij. Put

    U(x)=sum_i w_i(x) U_i,     V(x)=sum_i w_i(x) V_i.

Convexity preserves stochasticity and the desired interpolation. For one queried point take constant factors; zero queried points are trivial. Repeated queries at one location add no difficulty.

If X is a real-analytic embedded compact manifold, replace distance squared by ambient Euclidean squared distance. Then every q_i, w_i and factor is real analytic. For RP^d use its analytic embedding [u] -> uu^T in the real symmetric matrices. This avoids the nonanalytic intrinsic projective distance and verifies denominator positivity.

A deterministic adaptive algorithm run on the obstructed target produces a finite transcript if it terminates. Apply the construction to its actual queried points. The alternative returns exactly the same answers, so induction shows that the adaptive algorithm follows the same query path and terminates with the same answer. Thus it cannot distinguish the two models with a universally valid finite certificate. The alternative is constructed after the target run; this is legitimate for an impossibility statement over all possible candidates.

For a randomized algorithm the preceding argument proves only that **each realized finite transcript** admits an alternative. That alone does not establish a fixed alternative fooling the algorithm with high probability. The next theorem supplies the missing argument for smooth projective families.

## 7. Randomized finite-query impossibility with constant rank

Consider the projection family over RP^d, d>=1, in the seed. Let u be a unit representative in R^(d+1), let v be any fixed unit vector, and choose 0<eta<1. Choose a smooth function f:[0,1]->[0,1] equal to zero near 0 and equal to one on [eta,1]. Define

    t=v·u,
    z_v([u])=f(|t|) sign(t) u + [1-f(|t|)] v.              (E1)

The sign term vanishes in a neighborhood of t=0, so (E1) is smooth across that seam. It is unchanged by u -> -u. Also

    ||z_v||<=1,
    z_v·v=f(|t|)|t|+1-f(|t|)>0,

so z_v is never zero. With beta=alpha delta and the seed's positive constants, define global, labelled, smooth two-state factors

    U_0=(1/2,1/2),
    U_i=((1+alpha a_i·z_v)/2,(1-alpha a_i·z_v)/2),
    V_±=c±delta z_v.                                      (E2)

The vectors a_i form the fixed orthonormal basis of the zero-sum output space, under its identification with R^(d+1). Both factors are strictly positive and stochastic. Their table has centered rank one everywhere because z_v never vanishes. In fact, ||z_v||^2=f^2+(1-f)^2+2f(1-f)|t|>=1/2, since the two unit vectors being interpolated have nonnegative inner product. The unique centered singular value is beta||z_v||^2>=beta/2, so the candidate covariance gap is at least beta^2/4 uniformly in seam width and location. The impossibility therefore survives a fixed positive candidate gap, not merely constant rank. Whenever |v·u|>=eta, z_v=sign(v·u)u and (E2) gives **exactly** the target table.

Thus all disagreement is confined to the narrow projective band A_v={ [u]:|v·u|<eta }. If v is uniform on the sphere, every fixed [u] belongs to A_v with the same probability p_d(eta), tending to zero as eta tends to zero. In dimension one p_1(eta)=2 arcsin(eta)/pi. In general the coordinate density is

    Gamma((d+1)/2)/(sqrt(pi)Gamma(d/2)) (1-t^2)^((d-2)/2),

so p_d(eta)=O_d(eta) for eta<=1/2.

**Theorem D.** Let an adaptive randomized query algorithm terminate after finitely many parameter queries almost surely when run on the target. For every epsilon_0>0 there is a **single fixed** smooth globally two-state alternative of the form (E2) for which the entire transcript distributions have total variation distance less than epsilon_0.

**Proof.** Couple the algorithm's random seed under target and alternative. Let T be its query count on the target. Choose N_0 with Pr(T>N_0)<epsilon_0/2. Assume the usual measurability of algorithms and transcripts, and pad the target query sequence arbitrarily after it stops. The target's first N_0 queried points depend on its random seed but not on an independently sampled v. Conditional on those points, the union bound gives probability at most N_0 p_d(eta) of hitting the random band. Choose eta so this is <epsilon_0/2. Until the first band hit, all answers are identical, so adaptivity makes no difference: the coupled query paths agree. Averaging over v yields a disagreement probability <epsilon_0; hence at least one fixed v achieves it. Coupling bounds total variation. QED.

Therefore no test can simultaneously certify the target's global obstruction with error <=delta<1/2 and avoid false certification for every smooth two-state candidate, while stopping almost surely after finitely many queries on the target. Take epsilon_0<1-2delta. The alternative may have an arbitrarily large derivative; a common known modulus blocks the construction. Constant rank alone does not.

**Do not overclaim analytic randomized impossibility.** (E1) uses a smooth cutoff exact outside a band and is not analytic. The deterministic analytic interpolation theorem remains valid, but the randomized exact-real-oracle statement above is proved only for continuous/smooth alternatives. Analytic approximations could support a noisy/finite-precision version with additional arguments, not the same exact-oracle proof. Indeed, if the target analytic formula is known and an oracle returns exact real tables, every fixed distinct analytic candidate on connected RP^d differs from it outside a measure-zero analytic zero set. One random equality query then distinguishes that fixed alternative almost surely. Deterministic transcript interpolation and randomized identification therefore genuinely differ in this idealized oracle model.

## 8. Temporal laws and oracle boundaries

At each sampled parameter one can interpolate entire local stochastic instruments, not only single-read factors. If M_{i,y}^a are the queried parameter's nonnegative outcome-indexed k-by-k kernels with sum_y M_{i,y}^a row stochastic, set

    M_y^a(x)=sum_i w_i(x) M_{i,y}^a,
    pi_j(x)=sum_i w_i(x) pi_{i,j}.

Normalization and positivity are preserved. At every sampled x_i the whole model equals its local target model, so all horizons and adaptive within-experiment action policies agree exactly there. This makes Theorem C stronger than a finite-horizon table interpolation argument.

For the randomized construction use (E2)'s emissions and preparations in the seed's globally labelled hold/flip/refresh kernels. Outside A_v they equal the target's oriented local two-state mechanism; therefore **every** controlled output law at fixed x is identical. The coupling proof also works for stochastic output samples, using the same conditional samples until a band is queried.

The relevant oracle allows trials at chosen x with x fixed for that trial. Changing temporal action a is already included. A trial that sweeps x along a path while transporting an unobserved state is different: the seed does not specify transitions between fibers at distinct parameters, and no connection or parallel transport is determined by its fixed-parameter response laws. Such an experiment could provide new evidence, but cannot be silently assumed.

Finite temporal observations also cannot identify an unrestricted all-horizon mechanism in general. An a priori hidden-state bound or some other finite-realization promise is needed to turn finite-horizon agreement into all-horizon equivalence. The finite table bundle certificate is a necessary obstruction for any temporal realization containing those preparations and tests, not a sufficient reconstruction of dynamics.

## 9. What if the parameter topology is also unknown?

Theorems A–B assume K faithfully represents the experimental control space. If only a point cloud is supplied, there are two logically separate reconstruction problems:

1. recover an appropriate model of the base space and its cohomology;
2. recover the bundle/classifying map on that model from local observed subspaces.

Neither is possible from a finite cloud without geometric/regularity promises: unobserved handles, components, twists or tiny high-curvature regions can be inserted between observations. Bounds on reach/feature size, density and location noise can make a nerve or offset reconstruction valid. Bounds on the subspace map and measurement error then permit bundle reconstruction on it. These hypotheses cannot be established merely by observing that a persistence plot looks stable over a few scales.

Overlapping local test sets introduce another obligation: the subspaces must be compared through verified common observable coordinates or independently justified transition maps. Separately fitted latent labels on overlapping regions do not by themselves provide observable transition functions. The constructions here deliberately use globally fixed preparations and outputs, so the comparisons Q_v^TQ_w have an operationally specified common ambient space.

## 10. Primary-source ledger and novelty subtraction

- **Scoccola and Perea, Approximate and discrete Euclidean vector bundles**, Forum of Mathematics, Sigma 11 (2023), e20. Theorem 5.15 reconstructs bundles over sampled embedded manifolds under reach, density, noise and Lipschitz conditions. Section 6 gives stable algorithms for w_1, rank-two Euler class and w_2 from approximate cocycles. This directly precedes the finite-bundle/cocycle part of this note. [Primary paper](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/approximate-and-discrete-euclidean-vector-bundles/0FD787673265108D500C4D997F661F5C), [arXiv](https://arxiv.org/abs/2104.07563).
- **Tinarrage, Computing persistent Stiefel–Whitney classes of line bundles**, Journal of Applied and Computational Topology 6 (2022), 65–125. Gives stable and consistent bundle filtrations and effective line-bundle characteristic-class computation from finite data. [Primary preprint](https://arxiv.org/abs/2005.12543).
- **Davis and Kahan, The Rotation of Eigenvectors by a Perturbation. III**, SIAM Journal on Numerical Analysis 7 (1970), 1–46. Classical spectral-subspace perturbation source; the elementary ordered-gap estimate used above is spelled out rather than hidden behind an unspecified theorem constant. [Publisher](https://epubs.siam.org/doi/abs/10.1137/0707001).
- **Niyogi, Smale and Weinberger, Finding the Homology of Submanifolds with High Confidence from Random Samples.** Classical manifold sampling with quantitative reach and sample-density assumptions; one should not claim unknown topology is recovered without comparable assumptions. [Author-hosted primary manuscript](https://math.uchicago.edu/~shmuel/NSW1.pdf).
- **Hazewinkel, Moduli and canonical forms for linear dynamical systems II: the topological case** (1977). State bundles and failures of global continuous minimal matrix realizations are classical. Finite response/cocycle methods should not be presented as discovering a previously unknown local/global distinction in realization theory. [Institutional primary paper](https://ir.cwi.nl/pub/10022/10022D.pdf).
- **Balakrishnan, Rinaldo, Sheehy, Singh and Wasserman, Minimax Rates for Homology Inference** (AISTATS 2012), and **Balakrishnan, Rinaldo, Singh and Wasserman, Tight Lower Bounds for Homology Inference** (2013). These supply classical statistical indistinguishability/minimax precedents for topology under sampling and noise. Their passive manifold-sampling results do not by themselves establish this note's adaptive exact-query, fixed-base response-bundle no-go; the seam coupling proof is given separately. [Primary proceedings](https://proceedings.mlr.press/v22/balakrishnan12a/balakrishnan12a.pdf), [primary preprint](https://arxiv.org/abs/1307.7666).
- **Swan, Vector Bundles and Projective Modules** (1962), already discussed in the seed, supplies the projective generator obstruction. The characteristic-class resource lower bound is not new.

No literature claim of novelty is supported here. The most useful defensible contribution is a transparent combination: finite stochastic observations -> a margin-certified observable spectral cocycle -> a topological obstruction -> an explicitly normalized resource lower bound, with the evidence assumptions and impossibility boundary exposed. The randomized constant-rank smooth alternative is a sharpened empirical warning, not yet a sourced novelty claim.

## 11. Reproducible numerical smoke test

`topology_finite_example.py` generates 64 exact circle-family tables with beta=0.05, then runs the certifier using only those sampled tables, the circle mesh and the declared modulus. It checks an odd orientation cycle, a covariance error bound 0.0004432 below a quarter-gap of 0.000625, and a signal lower bound 0.04535. Candidates with Lipschitz constant at most 0.2 and zero vertex error have certified global centered error at most 0.02126, so two-state normalized models are excluded. The data-interpolant route passes independently. Results are in `topology_finite_example.json`. This is a floating-point smoke test, explicitly not a machine-verified interval proof.

`topology_euler_example.py` adds an independent rank-two test on 10,242 sampled sphere parameters and 20,480 triangles. Using a declared covariance modulus, it obtains a projector error bound 0.04312<1/20, solves the orientation cocycle from observed overlaps, and obtains integer Euler evaluation -2. Its candidate centered-error upper bound 0.00579 is below the signal bound 0.01958, excluding normalized three-state candidates with the declared fit/modulus. Results are in `topology_euler_example.json`. This also remains a floating-point smoke test. A nonzero Euler evaluation suffices for the resource obstruction; the specific absolute value 2 identifies this tested tangent-plane example, not every nontrivial oriented plane bundle.
