# Working theorem: controlled two-layer training quotients

Date: 2026-11-05. Status: derived here; historical novelty NOT established. Primary-source audit and independent check pending. This is not a programme-level completion claim.

## Exact setting and indices

Let m,n,h >= 1. Parameters A in R^(m x h), B in R^(h x n); observed matrix F=AB. At each step one may choose any target Y in R^(m x n) and perform simultaneous Euclidean GD for loss (1/2)||AB-Y||_F^2 with a fixed KNOWN eta != 0:
A_next=A-eta E B^T, B_next=B-eta A^T E, E=F-Y.
No momentum, weight decay, bias, constraints, or partial observation. F_0 is current output; F_1 after one update, F_2 after two. Behavioral equivalence means same F_k for every common target word Y_0,...,Y_(k-1), for all k>=0. Targets can be negative/unbounded. The theorem is exact-real-arithmetic. It does not provide robust identification from finite precision.

Define L=AA^T, R=B^TB, G=[[L,F],[F^T,R]]=[A^T B]^T[A^T B]. G is PSD and rank(G)<=h. Any such block G is realizable by a width-h pair.

## Closed dynamics (polynomial identities, every rank including F=0)

F_next=F-eta(LE+ER)+eta^2 E F^T E.
L_next=L-eta(EF^T+FE^T)+eta^2 E R E^T.
R_next=R-eta(E^TF+F^TE)+eta^2 E^T L E.

Proof: direct multiplication of the simultaneous updates. Thus equality of G implies equality of every future response, at any hidden width. No invertibility or genericity is needed.

## Theorem A: exact finite-step behavioral classification

If mn>1, the following are equivalent for two initial states, possibly of different hidden widths:
(1) equal responses for all finite common target words;
(2) equal F_0,F_1,F_2 for all target words of length at most 2;
(3) equal G.

If m=n=1, equivalence is instead equality of (F,S), S=L+R. A one-step experiment together with F_0 suffices; full G is generally not identifiable.

### Proof for mn>1

Equality of F_0 fixes F. Because Y is arbitrary, any residual E is available in both states. Equality of F_1 for all E gives delta L E+E delta R=0 for all E. Testing elementary matrices proves delta L=c I_m and delta R=-c I_n for one real c. (Off-diagonal entries vanish; all diagonal sums vanish.)

After a first common residual E, F_1 is the same, while
 delta L_1=c(I_m-eta^2 EE^T),
 delta R_1=-c(I_n-eta^2 E^TE).
Choose the next common target Y_1=F_1-Z so the second residual is any specified Z. The exact output difference after the second step is
 delta F_2=eta^3 c(EE^T Z-Z E^TE).
If n>1 use E=e_1 e_1^T and Z=e_1 e_2^T, for which the bracket is Z. If n=1 and m>1 use E=e_1 e_1^T and Z=e_2 e_1^T, for which the bracket is -Z. Because eta != 0, equality forces c=0. The converse follows from polynomial closure.

Although the proof chooses Y_1 using the common F_1, it is a legitimate witness to failure of equality for all fixed target words: once the pair and E are fixed, F_1 and hence Y_1 are fixed common matrices. No parameter-dependent inequality is smuggled into the equivalence definition.

### Scalar exception

For m=n=1, the closed recurrence is
 F_next=(1+eta^2 E^2)F-eta E S,
 S_next=(1+eta^2 E^2)S-4eta E F.
Thus equal (F,S) suffices forever. Taking any E != 0 recovers S from F_0,F_1. The one-dimensional bracket above always vanishes.

## Theorem B: continuous flow has a strictly coarser quotient

Consider controlled gradient flow at unit speed:
 dA/dt=-E B^T, dB/dt=-A^T E, E=AB-Y(t),
where target signals Y(t) are arbitrary piecewise-continuous matrices and comparison is on common intervals of existence. The closed Gram equations are
 dF/dt=-LE-ER,
 dL/dt=-EF^T-FE^T,
 dR/dt=-E^TF-F^TE.
Two states have identical F(t) under every such common control iff F is equal initially and L_2-L_1=c I_m, R_2-R_1=-c I_n for a constant c. Necessity follows from equality at t=0 and equality of initial derivatives for every constant target. For sufficiency, the shift is constant under the displayed equations and leaves dF/dt unchanged, so uniqueness of the polynomial controlled ODE gives equal F(t). This applies in every m,n, including scalar. For scalar the quotient equals (F,S), so discrete training adds no distinction there.

Hence for mn>1, observable minimization under controlled flow is strictly coarser than under fixed nonzero discrete GD whenever the feasible Gram cone admits a nonzero shift. Taking the continuous-training limit and forming the all-experiment behavioral quotient do not commute in this precise sense. This is not a claim that the discontinuity violates numerical convergence: the distinguishing signal is cubic in eta.

## Universal property and independent consequence

At fixed h the O(h) action is A -> A Q^T, B -> Q B. Equal G is equivalent to being in the same orbit, by the elementary equal-Gram/isometry-extension argument. Therefore for mn>1 the all-training behavioral quotient and this orthogonal orbit quotient coincide. Every set-valued invariant of the hidden orthogonal action factors uniquely through the behavioral quotient. Polynomial invariant theory also identifies G entries as generators, but the behavioral equivalence theorem above does not need that invariant-ring theorem.

Across arbitrary h, a behavior with Gram matrix G has smallest allowed hidden width max(1,rank G) when widths are required positive, or rank G if zero width is admitted. A rank factorization constructs it; any realization must have rank G<=h. It predicts the minimum hidden resources compatible with ALL discrete training behavior, not the installed width, since extra zero hidden units can always be added.

For scalar-scalar interfaces, every nonzero behavioral state (F,S), S>=2|F|, has a width-1 realization: choose a^2+b^2=S, ab=F. Thus rank of the actual 2x2 Gram matrix can differ within one behavior. The zero behavior has width 0 if permitted, else width 1.

## Explicit separation, no generic assumptions

Take m=1,n=2.
State P: h=1, A=[1], B=[0,0], so L=1,R=0,F=0, rank G=1.
State Q: h=2, A=[0,0], B=I_2, so L=0,R=I_2,F=0, rank G=2.
They have the same controlled-flow behavior by Theorem B (Q-P has c=-1). They also have the same entire one-step discrete response map.
Choose first residual E=[1,0], i.e. Y_0=[-1,0]. Both F_1=[-eta,0]. Choose second residual Z=[0,1], i.e. Y_1=[-eta,-1].
P has F_2=[-eta,-eta]. Q has F_2=[-eta,-eta-eta^3].
This proves a sharp two-step bound and a difference in minimum hidden realization width that NO controlled-flow experiment detects.

## Access and practical limits

Distinguish quantification over experiments from acquisition. A finite exact recovery protocol can use reset copies to recover F and the linear map K(E)=LE+ER from elementary residuals, then one two-step experiment to recover the sole shift. It requires full output matrices, arbitrary targets, known eta and exact reproducible initial state. Nonzero eta does not imply robust recoverability: the signal magnitude scales as |eta|^3 |c|, so fixed noise can hide the distinction. No observation of a single uncontrolled training trajectory is claimed sufficient.

## Primary-source comparison in progress

- Recovered corpus: learning_generated_characterizations.tex has an all-depth scalar-chain theorem and finite-step vs flow caveats; no matrix Gram two-step observability theorem was located by search. Its scalar chain has h=1 at each stage, unlike scalar input/output with arbitrary hidden width here.
- Marcotte, Peyre, Gribonval, Intrinsic training dynamics of deep neural networks, arXiv:2508.07370v2 / ICLR 2026: https://arxiv.org/html/2508.07370v2 . Inspected introduction, Theorems 3.8/3.9, and Appendix I. They explicitly use K(E)=LE+ER and its Kronecker representation in Appendix I equation (26). They study continuous intrinsic dynamics relative to output plus initialization/conserved data, not yet verified as stating the above finite-step all-starting-state classification. This is very close prior art and must be credited, not treated as unrelated.
- Orthogonal Gram quotient and invariant generation are classical invariant theory; no novelty is claimed for them or the behavioral quotient universal property alone.
- The candidate residual is the exact discrete/continuous quotient comparison, sharp horizon-two observability, dimension exception, and minimum-width consequence under the stated interface. Historical priority unresolved.

## Addendum: continuous controls and global existence

The flow theorem can dispense with the common-existence-interval qualification for locally bounded piecewise-continuous targets. Set V=(||A||_F^2+||B||_F^2)/2. Then
 V_dot=-2||F||_F^2+2<F,Y> <= (1/2)||Y||_F^2.
Thus V(t)<=V(0)+(1/2) integral_0^t ||Y(s)||_F^2 ds on every finite interval. No finite-time parameter blowup occurs. Piecewise-continuity gives the usual uniqueness; locally square-integrable controls can also be handled in the Caratheodory formulation. We do not quantify over arbitrary pathological non-integrable target signals.

## Addendum: exact noise barrier with bounded target norms

Use the explicit width-1/width-2 pair P,Q above, m=1,n=2, and constrain each target by ||Y_k||_F<=M with M>0. The first output is identical for every Y_0, since F_0=0 and K(E)=E. Write E=-Y_0. The common F_1=-eta E. For any common Y_1 the second residual is Z=-eta E-Y_1. Since EE^T E-E E^TE=0, the exact difference is
 delta F_2= -eta^3 c(EE^T Y_1-Y_1 E^TE), c=-1.
For arbitrary rectangular E,Z,
 ||EE^T Z-Z E^TE||_F <= ||E||_op^2 ||Z||_F.
Proof: take an SVD of E; in the resulting left/right bases, each entry of Z is multiplied by a difference of two squared singular values, each lying in [0,||E||_op^2]. The bound is sharp for mn>1 using the elementary E,Z in Theorem A.

Consequently, for the pair P,Q and these target bounds,
 sup_{||Y_0||_F,||Y_1||_F<=M} ||F_2(Q)-F_2(P)||_F = |eta|^3 M^3.
The maximum is attained by Y_0=-M[1,0], Y_1=-M[0,1]. Both targets have norm M independently of eta. This variant avoids the eta-dependent target Y_1 used for the simpler displayed outputs earlier.

Suppose each full-matrix output is corrupted by arbitrary additive Frobenius-norm error at most epsilon. The two candidate output balls intersect iff their centers have distance <=2 epsilon. It follows that:
- If |eta|^3 M^3>2 epsilon, one maximally separating two-update trial can robustly distinguish this pair, conditional on the declared candidates, step size, target calibration, and error model.
- If |eta|^3 M^3<=2 epsilon, NO protocol consisting of any number of reset experiments of depth at most two, even adaptively selected, can guarantee distinguishing this pair under adversarial bounded errors. At every first response the centers coincide; at every second response an adversary can report a common point in the intersecting balls. Identical histories cause adaptive policies to choose identical targets, continuing the ambiguity.

This is a sharp two-update observation-depth result, not an impossibility for arbitrarily long runs. Deeper experiments may accumulate a larger distinction. It also does not apply unchanged to independent stochastic noise, where repeated samples can average down the uncertainty. For fixed epsilon,M, the exact discrete distinction becomes unwarrantable by this entire bounded-depth experiment class as eta tends to zero, specifically whenever |eta| <= (2 epsilon/M^3)^(1/3).

The empirical target here is rank(G), the minimum width needed to reproduce all exact DISCRETE training responses. A continuous-flow equivalence class naturally has its own minimum realization width, which is constant on that class; we are not calling that invariant unidentifiable. Rather, flow observations cannot determine which discrete-behavior rank is present.

## Addendum: exact fixed-width boundary

At a fixed hidden width h, the discrete classification theorem remains valid. However, the strict comparison with flow can occur only when h>=max(m,n), besides mn>1. This condition is necessary and sufficient for a nonzero feasible Gram shift.

Necessity: if c>0 and G_2-G_1=c diag(I_m,-I_n), then L_2=L_1+cI_m is positive definite, and R_1=R_2+cI_n is positive definite. Hence m<=rank bound h and n<=h. For c<0 reverse the states. Sufficiency: with h>=max(m,n), realize G_P=diag(I_m,0_n) and G_Q=diag(0_m,I_n), padding factors with zero coordinates as needed. Their ranks are m and n and their difference is -diag(I_m,-I_n).

Thus at fixed h<max(m,n), feasible flow-equivalence already forces G equality, even though the unrestricted linear Gram equations have a formal shift direction. At h>=max(m,n), mn>1, that direction is genuinely realized and discrete training separates it. The m=1,n=2 example can be given with the SAME installed width h=2: pad P to A=[1,0], B=0_(2x2), while Q remains A=[0,0], B=I_2. The minimum exact-discrete realization widths remain 1 and 2. Installed width is never identified because padding is unobservable.

## Addendum: changing the target is essential for the explicit pair

For the P,Q width-1/width-2 pair, each stationary target Y in R^(1x2), held unchanged for an arbitrarily long run, yields identical discrete output sequences. Thus repeating training against one target, even with arbitrarily many steps and resets to try different stationary targets, does not distinguish this pair. The theorem's two-step experiment requires a target change within one run.

Proof: for Y!=0 set v=Y^T/||Y||. Both trajectories stay in a subsystem whose output is a scalar multiple of v^T. In P the active scalar factors initially have norms 1 and 0; in Q they have norms 0 and 1. The remaining hidden directions in Q are orthogonal and never contribute to output under this fixed target. Their effective scalar states therefore have the same (F_scalar,S)=(0,1). The scalar recurrence proves equality at every step. Y=0 is stationary at F=0. Equivalently use an orthogonal input change carrying Y to (||Y||,0), after which both systems reduce to swapped scalar layers and an unexcited perpendicular component.

This is not a claim that stationary targets never distinguish arbitrary pairs. It isolates a regression pair for which changing the intervention direction is indispensable.
