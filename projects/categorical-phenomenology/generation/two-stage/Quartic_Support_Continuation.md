# Two-stage continuation: discovered components to a forced shared-source law

Derived 2026-11-04. Mathematical proof and source/access audit. This is a new continuation relative to the inspected project artifacts, not a literature-priority claim. Orthogonal tensor decomposition and support recovery from nonnegative moment identities are classical.

## 1. What the earlier work already established

- `incomplete_probe_delivery/Incomplete probe decomposition results.txt` and the extracted `incomplete_probe/main/Vector_Directional_Theorem.md` derive the unique coarsest task-preserving conditional quotient from single/pair response laws. The strongest fixture discovers eight arbitrarily labelled states reducing to four, while the four-state quotient retains rank-two shared influence. Candidate patches, affine source response, rank, and context coverage are assumptions.
- `incomplete_probe/gluing/Matrix_Atlas_Classification.md` gives exact shared-frame gluing. A connected bipartite observation graph leaves one GL(r) parameter; a consistent odd cycle restricts it to one common orthogonal parameter, before coupled stochastic positivity is imposed.
- `incomplete_probe/stress/Matrix_Gauge_Family.md`, sections 5 and 9, already uses one quartet statistic to distinguish two fixed-source worlds that all pair histories miss. Repeating the quotient, gauge, or this two-world distinction is not new work.
- `evidence_certificate_delivery_20261030/sources/two_sided_linear_evidence_theorem.md` already has a complete fixed-loop two-sided linear KI mission criterion, rank-one adverse completions, the optional strict inverse guard, and exact known-context transport. It explicitly does not prove arbitrary unknown-network closure.

The continuation below takes the discovered conditional quotient as a legitimate working object, observes a new admitted four-way law, and infers a previously unspecified positive source law. It then predicts an unmeasured six-way law. No exact latent-state realization is assumed to be available to a controller.

## 2. Operational and mathematical hypotheses

There are N instrumented finite patches, N at least six for the held-out six-way test. At each update one source W in R^r is shared by all patches. At pre-update local context c_i, the retained quotient output V_i has conditional distribution

    K_i(v | c_i, W=w) = B_i(v | c_i) + [G_i(c_i) w]_v.

Rows sum to one, and all kernels used are nonnegative on the source support. Fresh patch outputs are conditionally independent given the SAME W and the contexts. Local baselines and response maps may depend nonlinearly on local state and inputs. Inputs precede the current draw; instantaneous output feedback is not implicitly admitted.

The source is IID across updates, independent of the pre-update contexts, with an initially UNKNOWN distribution mu satisfying

    E W = 0,  E WW^T = I_r,  ||W|| <= R almost surely.

The Euclidean support bound R is a declared, justified model constraint, not inferred merely from missing observations. Necessarily R^2 >= r. An alternative temporal hypothesis needs a separate argument; an unconditional quartet marginal does not identify arbitrary source memory.

The first-stage experiments have certified a nonempty joint completion family and discovered a conditional quotient. The relevant quotient response maps retain rank r. Pair measurements on a connected nonbipartite graph determine all G_i(c_i) in one common orthonormal source chart, up to a common orthogonal change. If the initial graph is bipartite, the marginals of an admitted full quartet add a same-parity pair and hence an odd cycle. Compatibility and positivity must still be checked jointly.

At four actually accessible simultaneous contexts, EACH of the four maps G_1,...,G_4 at its SINGLE physical context has column rank r. All four contexts must be simultaneously realizable under the same conditional source regime; observation selection must not change that source law. Let L_i G_i=I_r. It is not enough that G_i is full rank only after stacking inaccessible or mutually exclusive contexts. The fourth tensor is recovered from the observed full quartet law by the computable scores

    Phi_i(v) = L_i (e_v - B_i),
    T = E[Phi_1(V_1) tensor ... tensor Phi_4(V_4)] = E W^(tensor 4).

The equality follows by conditional independence and E[Phi_i(V_i) | W]=W. This is a statistical score applied to ordinary outputs, not an observation of the actual W. Sensor-noise calibration may be absorbed into the scores if its valid left inverse and conditioning bounds are supplied. Conditioning on hidden old states may be done by justified joint old/next-sensor deconvolution, not by pretending hidden states can be prepared or individually decoded.

All guarantees below concern the retained conditional model and this evidence family. They do not identify physical ownership, arbitrary unmodeled causes, or unique microscopic mechanisms.

## 3. Exact support theorem, all r

Suppose the quartet tensor admits an orthonormal frame o_1,...,o_r such that

    E (o_j^T W)^4 = R^2,  j=1,...,r.

These r diagonal conditions suffice. In particular they follow from T=R^2 sum_j o_j^(tensor 4). Write Z_j=o_j^T W and s=sum_j Z_j^2. Then EVERY compatible source law is exactly

    P(W=+R o_j)=P(W=-R o_j)=1/(2 R^2),
    P(W=0)=1-r/R^2.

Proof. Each random variable Z_j^2(R^2-Z_j^2) is nonnegative, because |Z_j|<=R. Its expectation is R^2 E Z_j^2-E Z_j^4=0. Therefore Z_j belongs to {0,+R,-R} almost surely. The ball bound forbids two nonzero coordinates simultaneously. The variance identity fixes the total probability on the jth signed pair to 1/R^2. E Z_j=0 gives equal positive/negative weights. The leftover mass is at zero. This also proves all off-diagonal fourth-moment identities without measuring them separately. QED.

For T=R^2 sum o_j^4, the quartic polynomial on the unit sphere is R^2 sum_j (o_j^T u)^4. Its maxima are precisely the signed axes. Thus the axis set is uniquely determined up to signed permutation. This is classical uniqueness of an orthogonally decomposable even-order tensor. Under an UNKNOWN source-law universe, the physical response frame and source law are not separately identified: only their common-chart positive mechanism and resulting output laws are identified.

One must check that the finite atom kernels B_i+G_i(R o_j) and B_i-G_i(R o_j) are nonnegative for every declared context. If an actual compatible model exists and all atoms have positive weights, exact positivity follows; a reconstructed numerical candidate should nevertheless expose this check. An empty completion family is rejected, not certified by vacuity.

## 4. Approximate support theorem with a dimension-explicit bound

In an orthonormal candidate frame suppose the TRUE source still obeys the exact mean, covariance, and ball constraints, and

    |E Z_j^4 - R^2| <= eta_j.

Set d_j=R^2-E Z_j^4, delta=sum_j d_j. The support bound gives d_j>=0, so 0<=delta<=sum_j eta_j (at most r eta under uniform error).

Define nonnegative polynomials

    A(Z)=s(R^2-s),
    D(Z)=s^2-sum_j Z_j^4=sum_(i!=j) Z_i^2 Z_j^2,
    q(Z)=A(Z)+D(Z)=R^2 s-sum_j Z_j^4.

Then E q=delta, so E A<=delta and E D<=delta. This improves the coarser entrywise-tensor bounds E A<=r^2 eta and E D<=r(r-1)eta: the ball bound couples all entries and diagonal saturation already controls their sum.

Let S={0,+/-R e_j}. Let U be nearest-point rounding of Z to S, with deterministic tie-breaking. It maps to zero when max_j|Z_j|<=R/2, and otherwise to the signed axis with largest absolute coordinate. The pointwise sharp inequality is

    ||Z-U||^2 <= (4/(3 R^2)) q(Z).

Proof. Scale R=1, let m=max_j Z_j^2 and a=sqrt(m). Since sum_j Z_j^4<=m s, q>=s(1-m). If a<=1/2, the nearest atom is zero and q>=3s/4. If a>1/2, the nearest squared distance is 1+s-2a. The inequality

    1+s-2a <= (4/3)s(1-a^2)

holds for a^2<=s<=1: the difference of right minus left decreases with s, so its minimum is at s=1 and equals (2/3)(1-a)(2a-1)>=0. Restore R. Equality occurs at Z=(R/2)e_1, showing sharpness of 4/3. QED.

Consequently

    e2 := E||Z-U||^2 <= 4 delta/(3 R^2) <= 4r eta/(3R^2).

This implies P(dist(Z,S)>=kappa)<=4 delta/(3 R^2 kappa^2), for any kappa>0. It does NOT imply exact finite support when eta>0.

Separate geometric forms, useful when only weaker defect bounds are available:

- For 0<a<=R^2/2, P(a<=s<=R^2-a)<=E A/[a(R^2-a)].
- Let d_axis^2=s-max_j Z_j^2. Since D>=s d_axis^2, for s0>0 and kappa>0,
  P(s>=s0 and d_axis>=kappa)<=E D/(s0 kappa^2).

## 5. Approximate weights and positive output prediction

Let nu be the distribution of U, and mu_* the exact sparse-axis law in section 3. Write t_j=nu(+R e_j)+nu(-R e_j), b_j=nu(+R e_j)-nu(-R e_j). Then

    sum_j |t_j-1/R^2| <= 2 sqrt(e2)/R,
    sum_j |b_j| <= sqrt(r e2)/R.

The first follows from sum_j|U_j^2-Z_j^2|<=||U-Z||(||U||+||Z||)<=2R||U-Z||. The second uses E Z=0 and ||E U||_1<=sqrt(r)||E(U-Z)||_2. The zero-atom discrepancy is at most the first sum. Therefore

    TV(nu,mu_*) <= (2+sqrt(r)/2) sqrt(e2)/R,

with the bound capped at one. Thus weak source concentration also fixes the positive/negative weights approximately; signs are not obtained from fourth moments alone but from the independent mean-zero condition.

For any k simultaneously conditionally independent retained outputs, suppose their true kernels are stochastic at all atoms in S as well as on the true support. Put ell_i=(1/2)||G_i||_(2->1). Product-kernel coupling and the previous bounds give

    TV(P_true^(k), P_*^(k))
      <= min(1, [sum_i ell_i + (2+sqrt(r)/2)/R] sqrt(e2)).

Here P_* is the explicit mixture over 2r+1 atoms with the weights above. No exponential global state enumeration is needed to represent the generator, though enumerating an entire N-output table is still exponential. If estimated stochastic kernels have per-atom TV error at most nu_i, add sum_i nu_i. Approximate positivity is a separate check; affine formulas must not be called probability kernels merely because they fit moments.

If mean/covariance are themselves only approximately normalized, the exact support theorem does not apply as written. For ||E Z||_2<=epsilon_m and diagonal covariance error sum_j|E Z_j^2-1|<=epsilon_v, the weight-TV bound gains epsilon_v/R^2 + sqrt(r) epsilon_m/(2R), in addition to the rounding term. The defect E q must be computed using the actual second moments, with their uncertainty propagated. A coordinate chart that is not orthogonal can also change the ball bound; do not silently retain R.

## 6. Held-out sixth and other higher moments

In the exact case,

    E W^(tensor 2m) = R^(2m-2) sum_j o_j^(tensor 2m),
    E W^(tensor (2m+1)) = 0,

for m>=1. In particular E Z_j^6=R^4. Six distinct full-rank output patches at admitted simultaneous contexts therefore have

    E product_(i=1..6) [e_j^T L_i(e_(V_i)-B_i)] = R^4.

This is a genuinely held-out consequence if only one-, two-, and four-patch laws were used in fitting. Six-way access and conditional independence of all six must be declared. EACH of the six response matrices must have rank r at its one selected physical context, and all six contexts must be simultaneously realizable under the same source regime without sampling-induced changes. The old r=2 matrix U with four rows has rank two at every displayed context because its gain s(c)>0. Six distinct patches extend the old four-module numerical fixture; no new physical six-view data have been collected or analyzed here. Scores may have large norm under weak response/calibration, so formal identifiability is not inexpensive estimation.

There is a particularly strong approximate axis prediction. For m>=2,

    0 <= R^(2m-2)-E Z_j^(2m)
      <= (m-1) R^(2m-4) d_j.

Proof. Apply R^(2m-2)-x^(2m-2) <= (m-1)R^(2m-4)(R^2-x^2) for |x|<=R, multiply by x^2, and use E Z_j^2=1. Thus

    0 <= R^4-E Z_j^6 <= 2 R^2 eta_j.

For odd moments, mean zero is essential. Cauchy-Schwarz gives

    |E Z_j^(2m+1)| <= m R^(2m-2) sqrt(d_j (R^2-1)).

This follows by subtracting R^(2m)E Z_j=0 and factoring the difference of powers. It supplies an approximate rather than exact symmetry conclusion.

## 7. Calibration and table error are part of eta

The previous theorems concern true source moments. Fitting an estimated fourth tensor to a sparse-axis tensor does not by itself establish the hypotheses.

At the four selected contexts, let the estimated score map be Lhat_i(e_v-Bhat_i). Suppose there is ONE common true orthogonal chart O such that

    ||Lhat_i G_i-O||_op <= kappa_i,
    ||Lhat_i(B_i-Bhat_i)||_2 <= beta_i.

These are quantitative shared-frame/calibration guarantees requiring rank and conditioning margins. They cannot be inferred solely from the quartet residual. Put a_i=kappa_i R+beta_i and b_i=max_v ||Lhat_i(e_v-Bhat_i)||_2. If the raw quartet table has one-norm error at most rho, its transformed fourth tensor has entrywise error at most rho product_i b_i. Conditional expectation of each score differs from OW by at most a_i; multilinearity gives a further error at most

    product_i(R+a_i) - R^4.

Thus, if the empirical tensor is within eta_fit per relevant diagonal entry of R^2 sum_j o_j^4, a valid choice is

    eta_eff = eta_fit + rho product_i b_i + product_i(R+a_i)-R^4.

The norm bounds hold uniformly under an orthonormal rotation chosen from the data, so this formula does not quietly presume the axes were fixed before fitting. A confidence guarantee still needs a simultaneous event for table, baseline, and common-frame estimates. If conditional tables are obtained by dividing joint frequencies, context floors and calibration/deconvolution errors must already enter rho and the other bounds. This note does not establish a finite-sample pair-factorization algorithm or infer physical source bounds from data.

An implementable confidence check after valid calibration can use sample splitting. Infer the common chart and candidate axes from training data, then FREEZE them. For N independent validation quartet windows at the required contexts, each diagonal-score product is in [-M,M], M=product_i b_i. Hoeffding plus a union bound over the r frozen axes gives simultaneous error at most t with probability at least 1-alpha when

    N >= (2 M^2/t^2) log(2r/alpha).

Add the common-frame/centering error product_i(R+a_i)-R^4 and the failure probability of the independent calibration event. A valid upper bound on each deficit d_j is max(0,R^2-T_j,emp+t+calibration_error). If the confidence intervals contradict the model-imposed upper bound R^2, report inconsistency rather than clipping away evidence. Dependent trajectory windows need a justified replacement concentration bound. No finite N proves an exact zero deficit, and a small deficit may require very large N because the left inverses amplify weak responses.

## 8. Why saturation and the source constraints matter

Two symmetric scalar laws supported in [-sqrt(3),sqrt(3)] have the same mean zero, variance one, and fourth moment two:

- A: mass 1/2 at zero and mass 1/4 at each of +/-sqrt(2).
- B: mass 1/3 at zero, mass 1/4 at each of +/-1, and mass 1/12 at each of +/-sqrt(3).

Their sixth moments are respectively four and five. The bound has R^2=3, and the fourth moment two is UNSATURATED. Four-patch laws in an affine conditionally independent model agree, but a six-patch experiment can differ. Therefore finite low-order moments in general do not determine the retained source law. The support-saturation condition is a substantive constraint, not decorative notation.

A radius counterexample directly matches the old tau=3/4 fixture and grows with r. The target law has R^2=4r/3, mass 1/4 at zero, and mass 3/(8r) at each +/-R e_j. The alternate law has mass 1/6 at zero, mass 1/(3r) at each +/-sqrt(r)e_j, and mass 1/(12r) at each +/-sqrt(2r)e_j. Both have mean zero, covariance I, every fourth diagonal 4r/3, every mixed fourth moment zero, and identical moments through order four. But their sixth diagonals are respectively 16r^2/9 and 2r^2. The alternate law fits the larger radius sqrt(2r), not the target radius sqrt(4r/3).

For r=2 this is sixth diagonal 64/9 versus 8, with the alternate radius 2. Thus the independently justified bound sqrt(8/3) does real identifying work in the old fixture. These are genuine positive affine-output alternatives: for example take 2r output symbols, baseline 1/(2r), response rows +/-epsilon e_j^T, and epsilon=1/(8r^2). All output probabilities are positive on the larger ball because epsilon sqrt(2r)<1/(2r), and the response has rank r. Conditional independence makes their complete output laws agree for up to four distinct patches, while a six-view score separates them. This is not merely a pair of abstract moment lists.

## 9. Prior-art boundary

The October stress fixture assumed the full source law in advance: Z in {0,+/-e_1,+/-e_2}, P(0)=1-tau and P(+/-e_j)=tau/4. At tau=3/4 this is a five-point law with covariance cI, c=3/8. Standardizing W=Z/sqrt(c) gives R^2=1/c=8/3, fourth diagonal 8/3, and sixth diagonal 64/9. The current premise is genuinely weaker: it retains only IID, mean zero, covariance cI, and the ball ||Z||<=1, allowing rotated-axis, continuous, and many other source laws. The measured quartet saturation, rather than an assumption of five-point support, forces the old five-point law in the learned response chart. The ball bound remains a strong external assumption. If the radius is only bounded by a larger slack value, the saturation certificate may fail even when the true law happens to be five-point.

The companion `check_quartic_support.py` uses rational arithmetic to verify this old tau=3/4 instance, full-rank four-view tensor extraction, simulated six-view predictions, an approximate rotated mixture, and the unsaturated scalar counterexample. It does not stand in for the universal proof or for a physical experiment. Its six-view table is generated from the inferred model, not newly collected held-out evidence.

Orthogonal tensor recovery from observable moments is established: Anandkumar, Ge, Hsu, Kakade and Telgarsky, *Tensor Decompositions for Learning Latent Variable Models*, JMLR 2014, https://www.jmlr.org/papers/v15/anandkumar14b.html . Their framework supplies the relevant classical baseline, not a guarantee for this entire operational pipeline without checking its assumptions.

Support localization by zeros of nonnegative moment polynomials is classical moment-problem reasoning. Curto and Fialkow, *Solution of the Singular Quartic Moment Problem*, equation (1.2), explicitly relate moment-matrix kernel polynomials to the support of a representing measure: https://www.cs.newpaltz.edu/~fialkowl/files/tcmp6.pdf . The short proof here uses only elementary bounded-support saturation; no new general moment theorem is claimed.

What is new relative to the inspected project package is the explicit bridge: previously discovered conditional quotient and jointly compatible pair frames -> admitted quartet observation -> source-support/weight certificate over an initially nonparametric bounded-law family -> positive whole-family generator and held-out six-way prediction, with an explicit approximate certificate. Literature novelty remains unassessed beyond these close baselines. This is an exact conditional mathematical result plus a proposed operational validation, not an executed physical experiment or a general unknown-architecture discovery theorem.
