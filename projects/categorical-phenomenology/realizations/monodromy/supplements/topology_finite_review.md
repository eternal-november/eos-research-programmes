# Adversarial review: finite response-bundle certificates

**Supplement snapshot:** contextual research material, not exact-hash-certified against the final circle review. The final report in the package root takes precedence. See ../SOURCE_STATUS.md.

**3 November 2026. Verdict: all substantive claims reviewed pass, including the added rank-two Euler certificate. No novelty clearance.** The strongest results are conditional certificates and matching impossibility statements, not recovery of topology or exact rank from unrestricted finite observations. Numerical tests below supplement the proofs; they are not interval-arithmetic certificates.

Historical reviewed revision (not the current supplement hash): `topology_finite.md`, SHA-256 `f9155a35170658255e9b3cd07c1dbc885af810fcf1cff9432d719579c7d3c9b0` (including the rank-two Euler extension). The reviewed revision resolves the only definition issue found: the maximum defining `d_v` is assigned zero at isolated vertices. It also clarifies randomized runs that terminate before `N_0` queries by padding the list after termination and explicitly assuming measurability. Neither adjustment changes a substantive result.

## 1. Spectral and orientation certificate

The covariance error bound is correct:

`||B(x)^T B(x) - B_v^T B_v|| <= (2||B_v|| + xi)xi`.

The later optional direct-covariance bound `omega_G(h)+(2||B_v||+epsilon_B)epsilon_B` is also valid by splitting spatial variation from the vertex sampling error. Here `||C||=sqrt(p)`, and `xi=sqrt(p)(epsilon+omega(h))` follows from the noise and truth-modulus assumptions. As usual, the supplied metric must give the intended topology and the modulus must tend to zero at zero. These are model assumptions, not estimated properties of the samples.

The displayed Davis–Kahan bound is valid in operator norm. For the top-r eigenbasis U of A and bottom-complement eigenbasis V of A+R, the Sylvester equation for `V^T U` has ordered spectral separation at least `gamma-e`. The integral solution gives `||V^T U|| <= e/(gamma-e)`. The equality between this norm and the distance of equal-rank orthogonal projectors then gives (A3). This argument does not require distinct eigenvalues inside the selected group.

Consequently `q_v<gamma_v/4` guarantees a positive actual spectral gap and projector error strictly below `1/3` on each vertex star. The positive r-th eigenvalue also puts the spectral bundle in the zero-sum output space. Lower singular modes may appear and disappear without affecting this separated bundle. With nonzero residual modes the specified Euclidean observable metric is part of the definition; the reviewed text includes this qualification.

The overlap argument contains the necessary steps, not merely a visual closeness heuristic. At a common point,

- `||P_v-P_w||<2/3`, so `sigma_min(Q_v^T Q_w)>sqrt(5)/3`;
- `||Q_v^T P(x)Q_w-Q_v^T Q_w||<1/3` because `Q_v^T(I-P)=Q_v^T(P_v-P)`;
- the connecting matrix segment is invertible, so its determinant sign cannot change;
- multiplying on either side by the positive normalizing matrices does not change determinant sign.

Thus each sampled sign is the sign of the genuine transition between the canonical actual frames. Genuine transitions obey the triangle identity. Open vertex stars of a finite simplicial complex and their nonempty intersections are contractible, and their nerve is K. The exact cocycle therefore represents `w_1`, with frame changes producing vertex coboundaries. Edges and triangles on the boundary of the complex cause no exception.

## 2. Normalization obstruction and finite candidate tests

Theorem B is valid even if only one factor is continuous and the other is discontinuous. The compressed map `P_F B'|E` is pointwise invertible because its perturbation is smaller than the uniform positive singular-value bound. If V' is continuous, `P_E V'^T|1_k-perp` is a continuous surjection; its image contains the adjoint of that compressed map because `U'^T C^T` takes values in `1_k-perp`. If U' is continuous, `P_F C U'|1_k-perp` is a continuous surjection onto F: subtracting a constant vector from `V'e` does not affect `CU'V'e`. Metric adjoints embed E or its isomorphic F into a trivial bundle of rank k−1.

No continuity of the product B' is needed in these containment arguments. No rank promise on B' is used. Normalization, not positivity alone, supplies the missing constant direction and the `+1` in `k>=g(E)+1`.

The finite-fit bound (B3), factor-modulus bound, data-reference bound (C2), and Hoeffding/union bound (D1) have the correct dimensions and constants. A truth modulus does not constrain an arbitrary candidate between vertices. Conversely, the barycentric reference can refute a bounded-modulus candidate class without any assertion about the actual continuum truth. This is logically different from identifying the true bundle. With both the truth and reference margins, projector distance below one supplies the claimed bundle isomorphism.

Finite data need not certify an exact centered rank. The separated spectral group is the appropriate object under the stated noise assumptions. The inequalities are sufficient and conservative, not necessary or optimal.

## 3. Characteristic-class witnesses

For rank one, the ordered simplicial Alexander–Whitney product really is

`a^d(v_0,...,v_d) = a(v_0,v_1)...a(v_(d-1),v_d)`.

The cocycle condition makes its evaluation on a mod-2 cycle a cohomological witness. If the line embeds in a trivial rank-s bundle, its rank-(s−1) complement has total class `(1+a)^(-1)`. Nonzero `a^d` forces `s−1>=d`, hence `k>=d+2`. The base need not already be identified as projective space, but the supplied complex and genuine cycle remain essential. A nonzero `w_1` for rank r only gives the weaker `k>=r+2` in general.

The warning about `TS²` is correct: both its Stiefel–Whitney classes vanish, while its integer Euler number is two. A zero orientation/cup certificate must not be treated as triviality evidence.

### Added rank-two Euler certificate

I independently checked the stronger margin and each conversion of norms. From `q_v<gamma_v/21`, put `e_0=max q_v/(gamma_v-q_v)<1/20`. For a rank-two canonical frame,

`||F_v-Q_v||_F² = 2 sum_j(1-cos(theta_j)) <= 4 e_0²`.

Thus sampled `A=Q_v^T Q_w` differs from the true transition `T=F_v^T F_w` by at most `4e_0` in Frobenius norm. A has positive determinant after solving and removing the orientation cocycle. Its polar factor R is unique, continuous, lies in SO(2), and minimizes Frobenius distance to the orthogonal group. The triangle inequality gives `||R-T||_F<=8e_0`. Since the distance of planar rotations is `2sqrt(2)|sin(angular_distance/2)|`, the angle error is at most `2asin(2sqrt(2)e_0)<0.284`.

This provides a single continuous actual angle lift on each overlap close to the chosen sampled edge angle. Reverse lifts must be defined by negation, including an edge whose chosen angle is pi; the revised text does this. On a triple overlap, the sum of actual lifts is an integer multiple of `2pi`, constant because the intersection is connected. The three-edge error is strictly below pi, so nearest-integer rounding returns that exact integer. On quadruple overlaps its coboundary vanishes by cancellation. This is a genuine Euler Čech cocycle, up to the specified orientation/sign convention, rather than a rounded empirical quantity merely assumed to be a cocycle.

Changing edge lift branches changes n by an integer coboundary. Changing oriented vertex frames preserves the Euler class; reversing the chosen bundle orientation changes its sign, independently on disconnected components. A nonzero integral cycle pairing is sufficient for nontriviality, but not necessary in the presence of torsion. The resulting `g(E)>=3`, `k>=4` conclusion is correct. It does not establish the separate three-state real upper bound for an unknown noisy truth.

## 4. Exact finite-query impossibility and quantifiers

The analytic interpolation construction is valid. For distinct sample points, exactly one product `q_i` is positive at each sampled point, and all products are positive elsewhere. The denominator never vanishes. Interpolating U and V separately preserves stochasticity and matches their product at every sampled point; matching the product away from those points is neither needed nor claimed. Squared ambient Euclidean distances give real-analytic functions on an analytically embedded manifold. The projective embedding `[u] -> uu^T` is appropriate.

For a deterministic adaptive exact-value oracle, run the algorithm on the target, construct the alternative from its finite target transcript, and induct on the queries. The algorithm then follows exactly the same path on that alternative. This is a valid `for every algorithm, there exists an alternative` impossibility proof. It does not imply a single alternative matching all randomized transcripts. It also does not apply to additional derivative, cross-parameter-transport, or globally described-function oracles without further work.

Theorem D supplies the missing randomized quantifier correctly. For each algorithm and each positive tolerance, first choose a high-probability finite target query-count cutoff, then choose the band width, and finally average over an independent direction v. This selects **one fixed alternative** whose disagreement probability is small over the algorithm's own random seed. The alternative is not selected separately for each realized run. No expected-query bound is required: almost-sure target termination gives the needed quantile. A possibly nonterminating alternative can be treated on the space of finite and infinite transcripts, so it does not invalidate the coupling or the certification-event contradiction.

The seam construction is smooth on projective space: the sign-dependent term vanishes near the seam, the formula descends under `u -> -u`, and `z_v dot v>0` prevents zero rank. Its norm is at most one, ensuring strict positivity of both factors with the stated seed constants. Its centered table is `beta (A^T z_v) z_v^T`, of rank one everywhere. In fact, a useful strengthening is immediate: `||z_v||²=f²+(1−f)²+2f(1−f)|v dot u|>=1/2`. The alternative's nonzero centered singular value is therefore at least `beta/2`, uniformly in the direction and band width. Its covariance spectral gap is at least `beta²/4`. Thus a fixed positive gap alone also does not defeat the impossibility. Outside the band the table is exactly the target table. The sphere-coordinate density and the special circle probability are correct.

The conclusion is minimax and class-wide: `for every finite-terminating randomized algorithm and tolerance, there exists a smooth two-state alternative`. It does not assert that one fixed alternative fools all algorithms or all tolerances. Smooth cutoffs do not prove the corresponding randomized analytic exact-oracle claim; the note correctly refuses that overclaim. A shared quantitative modulus excludes arbitrarily narrow seams.

## 5. Temporal oracle and prior-work boundaries

Finite-point interpolation of entire nonnegative outcome-indexed kernels preserves their stochastic sums. At each sampled parameter it agrees with the complete local instrument, so every finite horizon and adaptive within-trial action policy agrees there. For the smooth seam, the hold/flip/refresh kernels and preparations outside the band are either identical to the target's local representation or simultaneously conjugated by the sign swap. Telescoping proves equality of every controlled law. This is stronger than merely matching the one-read table. It requires the fixed-parameter oracle specified in the note; transporting a hidden state through varying parameters is extra structure.

[Scoccola–Perea (2023)](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/approximate-and-discrete-euclidean-vector-bundles/0FD787673265108D500C4D997F661F5C) already addresses finite noisy bundle information. Theorem 5.15 reconstructs bundles over sampled embedded compact manifolds under reach, density, observation-error, and Lipschitz conditions. Section 6 computes characteristic classes from approximate cocycles; Proposition 6.8 identifies the orientation construction, and §6.3 treats oriented rank-two Euler classes. The current note assumes a supplied base complex and derives subspace/transition margins from stochastic tables, then applies a normalized factorization obstruction. This is a useful interface composition, not evidence that finite bundle reconstruction or characteristic-class recovery is new. [Tinarrage](https://arxiv.org/abs/2005.12543) also supplies stable, consistent line-bundle filtrations and finite-data characteristic-class computation. No novelty claim follows from the sources checked or the absence of an exact matching formulation.

## 6. Reproducible independent checks

Run `python topology_finite_review_checks.py` (NumPy/SciPy). Results are saved in `topology_finite_review_checks_results.json`:

- 5,000 symmetric spectral perturbations, including internal eigenvalue multiplicities: all projector bounds pass.
- 2,500 arbitrary-gauge higher-rank overlap triangles: all determinant signs, invertibility bounds, and triangle identities pass.
- The six-vertex triangulated projective plane: 64 exact mod-2 cocycles, 32 coboundaries; all 46,080 cup-square evaluations across every vertex order agree with the nontrivial cohomology class.
- 4,470 analytic interpolation point checks: stochasticity and exact sampled products pass.
- 2,500 smooth seams: sign descent, nonvanishing, stochasticity, and rank-one checks pass; 1,205 outside-band cases verify every action/outcome kernel's conjugacy, and 6,025 controlled words match.
- 2,500 exact interval-union circle-band computations satisfy the coupling union bound.

Run `python topology_finite_euler_review_checks.py` (NumPy). Results are saved in `topology_finite_euler_review_checks_results.json`. A seven-times-subdivided octahedral sphere has 65,538 vertices, 196,608 edges and 131,072 triangles. Its outward fundamental integral cycle has zero boundary. The response-reference margin is `max(qbar/gamma)=0.0386353<1/21`, giving projector bound `0.040188<1/20`. After random local frame reflections, solving `a=db` restores orientation. The rounded polar-angle cocycle pairs to **−2**, consistently with the allowed sign convention. Arbitrary additional SO(2) vertex gauges leave that pairing unchanged. This independently tests the stronger certificate on an actual nontrivial rank-two bundle, not only random triangle data.

The 64-vertex circle certificate and later 10,242-vertex sphere Euler example were also rerun successfully. The latter uses a direct covariance modulus and obtains Euler pairing −2, projector error bound 0.04312 and a candidate-error margin below its signal bound. All floating-point outputs are regression evidence; certifying strict margins for an experimental claim still requires the promised interval/error bounds.
