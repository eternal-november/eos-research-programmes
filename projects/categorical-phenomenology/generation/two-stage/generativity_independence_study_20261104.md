# From a pair-observation chart to an executable independence test

Research note, 4 November 2026. This is a concrete two-stage generativity experiment, not a claim of a new ICA theorem or a solution to the broader reconstruction programme.

## Outcome

A pair-observation construction that deliberately retains an orthogonal ambiguity can be used to synthesize two observable fourth-order score matrices. Their commutator is independent of the arbitrary chart. A nonzero commutator rules out **every full-column-rank, r-dimensional independent-source realization** of the combined data, not merely two chosen orientations.

There is an explicit finite-output family for every r >= 2 in which all one-, two-, and three-patch laws agree between an independent-source world and a coupled-source world. The new four-patch experiment distinguishes them. The coupled family has positive categorical response probabilities and a commutator gap 8/(r+2)^2 in calibrated coordinates.

The same construction has a positive, conditional branch: under an additional independent-source promise with nonzero fourth cumulants, one generic contraction recovers the source directions up to signed permutation. The promise is not inferred from the first-stage data or from passing the fourth-order test.

## 1. Declared model and actual access

Fix one admitted context tuple. This can be one context in the prior conditional affine-source model; different contexts must not be pooled without the corresponding transport and common-moment assumptions.

There are four distinct, jointly measurable patches. Patch j has q_j categorical outputs, represented by its one-hot outcome e_(Y_j). Its conditional probability vector is

    P(Y_j = . | S=s) = b_j + A_j s,

where A_j is q_j by r and full column rank, 1^T A_j=0, and the displayed probabilities are nonnegative on the source support. The source satisfies E[S]=0 and E[SS^T]=I_r and has finite fourth moments. Patch outcomes are independent conditional on the same source occurrence S. Source coordinates are NOT assumed independent.

The population version initially supplies singles and simultaneous pair laws. The operation repertoire also permits collecting a simultaneous outcome from these four distinct patches and doing ordinary classical postprocessing. Initial lack of quartet evidence is not lack of quartet access. If quartet acquisition is not actually available, the proposed experiment is unavailable; the chart does not create this capability.

For the statistical claim, repeated quartet trials are independent at this context, or a separate valid concentration bound must replace Hoeffding. Hidden source memory, changing contexts, and unrelated runs cannot be silently ignored. There is no copying, hidden-state preparation, intervention, or decoding of a realized S.

The full-rank r-dimensional qualification matters. A larger, overcomplete independent generator not satisfying these rank promises is outside the exclusion theorem.

## 2. First passage: recover a shared Euclidean chart, not hidden coordinates

Singles determine b_j. Let x_j=e_(Y_j)-b_j and let

    D_ij = E[x_i x_j^T] = A_i A_j^T,  i != j.

A rank-r pair establishes r within the declared full-column-rank class. From three distinct patches construct

    G_1 = D_12 (D_32)^+ D_31 = A_1 A_1^T.

The identity uses (A_3 A_2^T)^+=(A_2^T)^+ A_3^+, valid because both factors have their indicated full ranks. Thus G_1 is positive semidefinite of rank r. Choose any rank-r factor B_1 with B_1 B_1^T=G_1 and set

    B_j = D_j1 (B_1^+)^T,  j=2,3,4.

There is one O in O(r) such that B_j=A_j O for every j. The choice of B_1 changes only this common O. This is the finite complete-graph instance of the prior matrix-atlas result, not a newly claimed first-stage theorem.

Define score maps L_j=B_j^+ and observable scores z_j=L_j x_j. These are functions of recorded categorical outcomes. They satisfy

    E[z_j | S]=O^T S,       E[z_i z_j^T]=I_r  (i != j).

A score is an unbiased conditional-mean representation, not an observation of S, a positive preparation, or an installed latent-coordinate sensor.

## 3. Second passage: use the chart to synthesize new experiments

For any specified g in R^r, collect a quartet and evaluate the matrix-valued statistic

    W_g = z_1 z_2^T (g^T z_3)(g^T z_4).

Define its fourth cross-cumulant contraction

    M_g = E[W_g] - ||g||^2 I_r - 2 g g^T.

The three subtractions are exactly the three cross-pair products; no same-patch repeated measurement is used. Conditional independence of the four patches gives

    (M_g)_ab = Cum((O^T S)_a, (O^T S)_b,
                   g^T O^T S, g^T O^T S).

In particular M_g is symmetric at population level. It can be symmetrized empirically. Only two r by r summary matrices are required for a two-direction test; a full q_1 q_2 q_3 q_4 table or r^4 cumulant tensor need not be stored.

If the chart changes by an orthogonal Q and directions are transported accordingly, M_g changes by orthogonal conjugation. Therefore vanishing and operator norm of [M_g,M_h] are chart invariant. For a fixed numerical g,h in a newly chosen chart, one is choosing possibly different intrinsic directions, but a nonzero result remains a valid basis-independent exclusion certificate.

### Theorem: a realization-invariant exclusion certificate

If any full-rank r-dimensional independent-source realization of the observed singles, pairs, and quartet statistics exists, then

    [M_g,M_h]=0 for every g,h.

Hence one measured nonzero commutator excludes all such realizations.

Proof. Standardize each independent source coordinate to variance one, absorbing scales into its response column. Its fourth-cumulant tensor is diagonal in its independent basis. In the common observed chart it has the form

    T = sum_i kappa_i q_i^(tensor 4),

where q_i are an orthonormal basis and kappa_i their fourth cumulants. Consequently

    M_g = sum_i kappa_i (q_i^T g)^2 q_i q_i^T.

All these matrices are diagonal in the same orthonormal basis and commute. Every compatible full-rank factorization of the same pair laws differs only by a common O, so a different hidden frame cannot evade the certificate. QED.

This does not require a source-independence promise. It tests that proposed stronger explanation within the original affine, shared-source universe.

### Exact algebraic boundary

For any symmetric fourth-order tensor T, all its contractions M_g commute if and only if T is orthogonally decomposable as above, allowing zero kappa_i.

For the reverse implication, simultaneously diagonalize the finite-dimensional span of the commuting symmetric matrices. In that basis, T_ijgg=0 for all g whenever i != j. Polarization gives T_ijkl=0 for i != j and every k,l. Full tensor symmetry lets any two unequal indices be moved into the first two positions, so every non-fully-diagonal entry vanishes.

This boundary is a fourth-order boundary, not a characterization of full statistical independence. For example, for r >= 5 the uniform law on sign vectors with product of all coordinates +1 is dependent but has the same moments through order four as independent Rademacher coordinates. No fourth-order procedure can certify their independence. Its finite support has 2^(r-1) points, whereas a nondegenerate r-coordinate product law has at least 2^r, so an invertible rotation cannot turn this law into an independent r-source law.

A finite deterministic exact check can use contractions g=e_i and g=e_i+e_j, whose gg^T span Sym^2(R^r). All pairs of the resulting matrices must commute. Alternatively, if T is not orthogonally decomposable, two continuously random directions have a nonzero commutator almost surely: at least one commutator entry is a nonzero polynomial in their coordinates. This is an exact-population statement, not a finite-noise acceptance guarantee.

## 4. A coupled growing family with strictly positive finite outputs

Let r >= 2, q=r+1, u=(1/q,...,1/q), and choose a q by r matrix U with U^T U=I and U^T 1=0. Let R_1,...,R_4 be arbitrary unknown orthogonal matrices and put

    A_j = lambda U R_j,
    0 < lambda <= 1/[2(r+1)sqrt(r)],
    K_j(a|s) = 1/q + lambda (U R_j s)_a.

All source values below have Euclidean norm sqrt(r). Therefore K_j(a|s) >= 1/(2q), and the entries sum to one. Each A_j has rank r. The four channels may have unrelated orientations.

Compare two source worlds with these same channels:

1. Independent world I_r: S is uniform on {−1,+1}^r.
2. Coupled world C_r: with probability r/(r+2), S is uniform on {−1,+1}^r; with probability 2/(r+2), S is uniform on {−sqrt(r)e_i,+sqrt(r)e_i: i=1,...,r}.

Both are centered, have covariance I, and are invariant under global sign reversal. Their third moments vanish. As a product of at most three affine channel probabilities depends only on source moments through degree three, **all one-, two-, and three-patch laws coincide**. This includes every pair used in chart construction.

For C_r, odd-coordinate fourth moments vanish,

    E[S_i^4] = 3r/(r+2),
    E[S_i^2 S_j^2] = r/(r+2) for i != j.

Thus with beta=−2/(r+2),

    T_ijkl = beta (delta_ij delta_kl + delta_ik delta_jl + delta_il delta_jk),
    M_g = beta (||g||^2 I + 2gg^T).

This tensor is rotationally invariant, even though the full source law need not be. The fourth-order dependence connects every pair of source directions and does not arise by appending independent extra coordinates to one fixed two-dimensional counterexample.

Take g=e_1 and h=(e_1+e_2)/sqrt(2) in any learned chart. Then

    [M_g,M_h] = 2 beta^2 (e_1 e_2^T - e_2 e_1^T),
    ||[M_g,M_h]||_op = 2 beta^2 = 8/(r+2)^2.

For I_r, the cumulant tensor is −2 sum_i q_i^(tensor 4) in the learned chart, so its contractions commute. The quartet experiment therefore distinguishes C_r from every independent-source explanation, rather than only from the displayed I_r example.

The source support has 2^r+2r points, but it has an O(r)-time sampler: choose the mixture branch, then sample independent signs or one coordinate and sign. The experimental and summary dimensions grow polynomially. The elementary finite-sample bound below is polynomial but deliberately conservative and expensive.

## 5. Noise and finite acquisition

### Sound certificate from calibrated matrix errors

Suppose confidence bounds give

    ||Mhat-M_g||_op <= epsilon,
    ||Nhat-M_h||_op <= epsilon.

Then

    ||[Mhat,Nhat]-[M_g,M_h]||_op
       <= 2 epsilon (||Mhat||_op+||Nhat||_op) + 2 epsilon^2.

It follows that the entirely computable strict inequality

    ||[Mhat,Nhat]||_op
       > 2 epsilon (||Mhat||_op+||Nhat||_op) + 2 epsilon^2

certifies a nonzero true commutator on that confidence event. Failing the inequality means inconclusive, not independent.

The bound follows by writing the true matrices as Mhat−E and Nhat−F, expanding the commutator, and using ||[A,B]|| <= 2||A||||B||.

### Conditional concentration with exact pair calibration

Suppose all four exact calibrated scores obey ||z_j|| <= R, and ||g||=||h||=1. For n independent quartet trials, each entry of symmetrized W_g and W_h lies in [−R^4,R^4]. Hoeffding, a union bound over 2r^2 entries, and ||E||_op <= r max_ab |E_ab| imply that both matrix errors are at most epsilon with probability at least 1−delta whenever

    n >= [2 R^8 r^2 / epsilon^2] log(4r^2/delta).

The same quartet sample estimates both contractions. This avoids pretending that a new physical operation is required for each tensor entry.

For the explicit categorical construction, R <= 1/lambda. In C_r the true contraction norms are 3|beta|. Taking epsilon=|beta|/16=1/[8(r+2)] guarantees the strict rejection inequality on the error event. Indeed the estimated commutator norm is at least (159/128)beta^2, while the threshold is at most (99/128)beta^2.

At lambda=1/[2(r+1)sqrt(r)], the sufficient bound becomes

    n >= 32768 (r+1)^8 r^6 (r+2)^2 log(4r^2/delta).

This O(r^16 log(r/delta)) sufficient bound is not a practical sample recommendation and is not claimed optimal. It explicitly exposes the high cost of weak categorical readouts.

### Estimated pair calibration

The preceding n counts quartet sampling only. Pair acquisition, singular-value conditioning, and calibration confidence must be charged separately.

One usable conditional wrapper is this: after a common orthogonal alignment, suppose the learned score maps obey ||zhat_j(a)−z_j(a)|| <= eta uniformly over all patch outcomes, with ||z_j(a)|| <= R. Using independent quartet data and the same Wick subtraction as the ideal chart, the deterministic error in the raw fourth-order contraction is at most

    epsilon_cal = (R+eta)^4−R^4 <= 4 eta (R+eta)^3.

This follows by telescoping a four-factor multilinear product. Use R+eta in the sampling bound, obtain epsilon_stat, and use epsilon=epsilon_stat+epsilon_cal in the sound commutator inequality. Calibration failure probabilities are added to delta.

A certified eta requires rank and conditioning margins and an honest confidence set or stable calibration procedure; it does not follow from finite data alone. Unknown baseline errors must be included in eta. Exact identities, tiny singular values, and shared source memory are not granted statistical guarantees by the present calculation. The prior three-view noisy-latent-state calibration could be placed before this construction, but its inversion and sampling costs would be additional.

## 6. Positive conditional branch

If the source coordinates are independently distributed and at most one fourth cumulant is zero, then for a continuously random g,

    M_g = Q diag(kappa_i (q_i^T g)^2) Q^T

has simple eigenvalues almost surely. For each pair i != j the collision equation is a nonzero polynomial unless both kappa_i and kappa_j vanish. A generic eigendecomposition therefore recovers the independent-source axes up to signed permutation. Equal nonzero kurtoses do not obstruct this generic contraction.

The recovered B_j q_i are channel response directions, not realized source values or intervention controls. If a simple-spectrum gap is gamma and a contraction error is epsilon<gamma/4, standard symmetric eigenspace perturbation gives direction error of order epsilon/gamma (for example sin angle <= 2epsilon/gamma after matching). Calibration error must also be included.

This is classical cumulant ICA applied after the prior chart construction. It is a positive second-stage construction, but its assumptions must not be smuggled into the first-stage evidence.

## 7. Relation to the 28 October result and prior art

The 28 October incomplete-probe result already establishes response subspaces, a common GL/O matrix atlas, and a four-patch distinction between two named r=2 rotated worlds. Those are not new here. The present construction stays inside its affine shared-source universe at one context tuple. It does not add source independence to obtain the rejection result.

What this particular experiment adds relative to that delivered fixture is:

- a chart-invariant computable criterion excluding an entire r-dimensional independent-source model class;
- an explicit coupled family for every r>=2, with strictly positive categorical channels and agreement of all laws through three patches;
- synthesis of the required scores from the observed pair chart, with no source coordinates supplied;
- a genuine four-distinct-patch acquisition protocol and a noise-aware one-sided certificate;
- an exact description of what a positive fourth-order result does and does not establish.

These are a constructive integration and a worked new application, not a credible priority claim. Fourth-cumulant diagonalization is the core of classical ICA/JADE. Orthogonally decomposable tensors already have algebraic characterizations, and multiview ICA has an extensive literature. The mathematical ingredients should be credited explicitly.

Primary sources checked on 4 November 2026:

- Miettinen, Taskinen, Nordhausen and Oja, *Fourth Moments and Independent Component Analysis*, Statistical Science 30(3), 2015, pp. 372–390. Develops fourth-moment ICA functionals, including FOBI, JADE and FastICA, their equations and asymptotic behavior. https://arxiv.org/abs/1406.4765
- Boralevi, Draisma, Horobet and Robeva, *Orthogonal and unitary tensor decomposition from an algebraic perspective*, 2015 preprint, published Israel Journal of Mathematics 222(1), 2017. Algebraic characterization of orthogonal decomposability and connections with associative algebras. https://arxiv.org/abs/1512.08031
- Pandeva and Forre, *Multi-View Independent Component Analysis with Shared and Individual Sources*, UAI 2023, PMLR 216, pp. 1639–1650. Identifiability and recovery for multiview noisy linear ICA with shared and individual sources. Its stated observation model is not the categorical conditional-mean model here; it establishes that multiview independent-source identification is a major existing baseline. https://proceedings.mlr.press/v216/pandeva23a.html

## 8. Verification and limits

`check.py` constructs the actual categorical joint laws for r=2,3,4,6,8 with unrelated random patch rotations. It reconstructs the chart using only pair laws, contracts the actual q^4 quartet law using the learned score maps, and checks the commutator gap. `results.json` records pair and triple agreement below 3e−17, independent-world commutators below 7e−13, and the predicted nonzero coupled-world values.

This is a floating-point regression check of finite cases, not formal proof, sampled-data validation, or human peer review. The proof above is general; the executable is a separate consistency check. No hardware experiment has been performed.

The generative step is real but bounded: an invariant structure inferred from incomplete evidence becomes a recipe for acquiring a new invariant and testing an entire proposed explanation class. It does not turn underdetermination into free physical access, prove unrestricted latent independence, or settle the broader native cross-doctrine reconstruction problem.

## 9. Audit of the original tau=0.75 origin-plus-axes fixture

The archived `stress/Matrix_Gauge_Family.md` and `stress/check_matrix_gauge.py` supply Z in {0,+e_1,−e_1,+e_2,−e_2}, with probabilities 1−tau at zero and tau/4 at each nonzero point. Standardize S=sqrt(2/tau)Z. Then Cov(S)=I,

    C1111=C2222=2/tau−3,
    C1122=C1212=C1221=−1,

with all fourth entries having an odd coordinate multiplicity zero. At tau=3/4,

    K11=T(:,:,e_1,e_1)=diag(−1/3,−1),
    K12=T(:,:,e_1,e_2)=[[0,−1],[−1,0]],
    [K11,K12]=[[0,−2/3],[2/3,0]],
    ||[K11,K12]||_op=2/3.

The mixed contraction K12 is an observable linear combination of rank-one contractions by polarization:

    K12=(M_(e_1+e_2)−M_e1−M_e2)/2.

Equivalently M_((e_1+e_2)/sqrt(2))=(K11+K22)/2+K12=−(2/3)I+K12, so its commutator with K11 also has norm 2/3. These numeric directions are in the displayed source-aligned frame. Pair observations alone do not supply that frame; in an arbitrary learned chart, use a deterministic spanning set of contractions or generic random directions. Non-orthogonal-decomposability, unlike the numeric expression, is frame independent.

Crucial predecessor qualification: this stress fixture explicitly DECLARES its entire origin-plus-axes source law and available regime probabilities. Its failure to admit independent standardized coordinates is therefore already a consequence of its structural input. One must not advertise the new test as discovering a previously unknown independence failure in that fixed-law fixture. The substantive unknown-source experiment above belongs to the broader affine shared-source class of the prior main vector theorem, in which only conditional mean/covariance are fixed and higher source moments remain unresolved.

The old rotated worlds both fail the independent-source criterion. The present criterion does not replace the old quartet statistic for distinguishing those two orientations; it answers a stronger model-class question after the source-law specification is correspondingly broadened.
