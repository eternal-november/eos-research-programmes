# Independent adversarial review: restricted-context support certification

Reviewed `world_theorem_frozen.md`, SHA-256 `11e397199b2464454e9027c64ce4bd0ec5f51cac7ab54f21bbf51a3e16b98edc`.

## Verdict

No blocking mathematical defect remains in the reviewed statement. The fractional-cut upper bound and balanced-null adaptive lower bound are valid under the exact fresh-unit context oracle. The displayed asymptotic order is justified. This is a certification theorem for a supplied pattern, not discovery of the pattern or identification of the unknown joint distribution. The proof mechanisms have strong classical predecessors; this review establishes no novelty clearance.

The initial abbreviated proposal risked four errors: applying the lower bound at an arbitrary biased null, omitting null completeness, confusing a strict certificate threshold with a testing boundary, and omitting integer rounding. The full reviewed version explicitly repairs all four. It also now states unconditional confidence coverage correctly.

## 1. Typed model and TV identity

The assumptions are substantive: one stationary joint law on the entire sign cube; a known sign pattern `s`; an independently fixed family of allowed contexts; a context selected before seeing a fresh unit; joint access to its coordinates on that unit; and no later access to other coordinates of that unit. Adaptivity across earlier units is allowed. Different contexts must not induce different latent laws.

Let `η=μ(Sᶜ)`, where `S={s,−s}`. For root `r`, the map `R_r(x)=(x_r/s_r)s` fixes every point of `S`. Its pushforward `q_r` is zero outside `S`, and on each point of `S` its mass is the original mass plus the nonnegative mass reassigned there. Thus the absolute mass difference outside `S` is `η`, and the absolute mass difference inside `S` is also `η`. Consequently `TV(μ,q_r)=η`. The marginal at root `r` uniquely specifies a law supported on the two points of `S`, proving the uniqueness assertion.

Indeed `inf_{ν:ν(S)=1} TV(μ,ν)=η`. The root projection is one minimizing redistribution. It is not generally a known distribution, need not be independent of the root, and need not be the balanced law. Therefore an accepted certificate warrants proximity to this class, or to the unknown `q_r(μ)`, without estimating its mixture weight.

## 2. Upper bound and confidence coverage

Normalize a state by `x_i/s_i`. Every bad state induces a nontrivial cut, up to complementation. Its restriction to context `C` violates local coherence exactly when `C` crosses that cut. Under probabilities `p_C=w_C/τ*`, every bad state is detected with probability at least `1/τ*`. Averaging over the unknown law gives a per-trial violation probability at least `η/τ*`.

The specified nonadaptive trials are independent, so the probability of no violation is at most `(1−η/τ*)^N`. This proves both the exact ceiling formula and the exponential relaxation. It also proves the stated confidence procedure: set `U_N=1` after any violation, and otherwise set it to `min(1,τ*(1−δ^(1/N)))`. For each fixed law, `P_μ(η>U_N)≤δ`. This is frequentist coverage across repeated data, not conditional coverage given acceptance.

The result is non-tolerant. It accepts every exactly coherent law, but need not accept every law with `η≤ε`. The zero-failure bound is for a prespecified sample size. Optional stopping, selecting `s` on the certification data, or searching many candidate patterns would require a separately justified procedure or correction.

## 3. Adaptive lower bound

The balanced null is essential. Let `q0` give equal mass to `s` and `−s`, and let `q_B` give equal mass to the two complementary patterns obtained by flipping a nontrivial cut. On a noncrossing context, the marginals of `q0` and `q_B` coincide. On a crossing context, their supports are disjoint. Hence the raw-observation KL from `q0` to `(1−ε)q0+εq_B` is exactly zero or `−log(1−ε)`, respectively.

For an arbitrary biased coherent null this zero-KL assertion fails: on a noncrossing context the balanced contaminant can change the sign bias. The theorem correctly uses a lower bound at `q0`, which is sufficient for a worst-case complexity conclusion, rather than a pointwise lower bound at every coherent law.

Under `q0`, a finite stopped transcript has likelihood ratio `(1−ε)^(−K_B)` against the cut alternative, where `K_B` counts sampled contexts crossing `B`. The action-selection and stopping kernels cancel because they are the same functions of the observed past under both laws. Taking expectation gives the transcript KL `E_q0[K_B]·[−log(1−ε)]`. Binary data processing for the acceptance event, together with completeness and soundness, gives at least `kl(1−δ,δ)`.

Writing `t_C=E_q0[N_C]`, the weights `t_C[−log(1−ε)]/kl(1−δ,δ)` are feasible for the fractional-cut LP. Summing proves the bound. The proof only needs null-to-alternative absolute continuity; reverse absolute continuity fails and should not be assumed. The finite expected stopping count and almost-sure stopping hypotheses make the stopped argument well-defined. If the null is accepted with probability one, the numerator can be strengthened to `log(1/δ)`.

Soundness alone is insufficient: an algorithm that never accepts is vacuously sound and needs no information. The reviewed theorem explicitly includes null completeness. For a certificate asserting `η≤ε`, its bad alternatives have `η>ε`; using mass `η>ε` and taking `η↓ε` gives the same lower bound. The reviewed statement includes this boundary argument.

For the parameter range `ε≤1/2`, `δ≤1/4`, the elementary comparisons `ε≤−log(1−ε)≤2ε` and `kl(1−δ,δ)=Θ(log(1/δ))` justify the claimed order. This compares a fixed-sample upper bound with a null-expected adaptive lower bound, not identical finite-sample optimization problems or matching constants.

## 4. Context geometry and edge cases

For finite `H` and `m≥2`, infeasibility is equivalent to an un-crossed nontrivial cut. If every cut has a crossing context, assigning weight one to every context is feasible. Equivalently, the hypergraph's coordinate connectivity is sufficient and necessary. On an un-crossed cut, the balanced coherent and balanced flipped laws have exactly the same available marginal laws. No amount of adaptivity or fresh sampling repairs this ambiguity.

For tree-edge contexts, deleting an edge determines a cut crossed by that edge alone. Thus every edge weight is at least one; unit weights attain `τ*=m−1`.

For all contexts of size `k`, with `2≤k≤m`, summing singleton-cut constraints gives `kΣw_C≥m`. Under equal context weights, the number of crossing contexts for a cut of size `b` is

`binom(m,k) − binom(b,k) − binom(m−b,k)`.

This is minimized at a singleton cut. For example, the sum of the two subtracted terms is a symmetric convex sequence in `b`, hence maximized at an endpoint of `1,…,m−1`. The minimum crossing count is `binom(m−1,k−1)`, so uniform weights attain `τ*=m/k`.

The exclusions matter. If `m≥2` and every context has size at most one, no cut is crossed and `τ*=∞`, not `m/k`. If one extends the theorem to `m=1`, every possible state is coherent and zero samples suffice; the current statement appropriately assumes `m≥2`. Full access `k=m` gives `τ*=1`. Duplicate contexts do not improve the LP.

The trial count is not a scalar-response count: all `k` responses in a context consume one prepared unit but `k` coordinate measurements. Computational effort to find optimal LP weights is also separate from the sample bound. A large or implicitly specified context family would need its own algorithmic model.

## 5. Independent finite checks

`world_review_checks.json` records exact rational checks of the projection identity in 20 nonuniform-law/root cases, 2,547 cut/context marginal comparisons, and the complete-uniform-family formula for 45 pairs `(m,k)` with `2≤m≤10`. All passed. These checks are diagnostics, not substitutes for the general proofs above.

## 6. Strongest-source comparison

The adaptive lower-bound mechanism is classical. Kaufmann, Cappé and Garivier's [2016 Lemma 1](https://www.jmlr.org/papers/volume17/kaufman16a/kaufman16a.pdf) relates expected experiment counts, per-experiment KL and the binary divergence of a decision event. Its printed statement assumes mutual absolute continuity, so it should not be invoked literally here. The direct stopped-likelihood proof supplies the necessary one-direction version. Garivier and Kaufmann's [2016 lower-bound proof](https://proceedings.mlr.press/v49/garivier16a.pdf) then optimizes the expected sampling proportions against all alternatives. The present LP is this standard design principle specialized to a zero-or-constant KL incidence matrix. This is a strong overlap, not a citation establishing the exact theorem verbatim.

[Controlled Sensing for Multihypothesis Testing](https://arxiv.org/abs/1205.0858) studies adaptive observation selection and sequential testing, with Chernoff-based asymptotic guarantees. Its abstract establishes the surrounding predecessor; its precise theorem hypotheses were not audited for literal applicability to this composite support property.

Goldreich and Ron's [Testing Distributions of Huge Objects](https://theoretics.episciences.org/12765/pdf), particularly its model and support-property discussion, makes local inspection of sampled bitstrings and support on a known string property established territory. Its main metric is Hamming earth mover; it explicitly discusses total variation as the discrete-metric specialization. Its oracle permits multiple coordinate probes into sampled objects, unlike the restricted one-context fresh-unit interface here. It does not by that fact supply this exact hypergraph-cut complexity formula. Nor may a difference of interfaces alone be treated as novelty evidence.

The title “fractional cut cover” is potentially ambiguous: some graph literature uses it for weighting cuts to cover edges, the transpose of the present operation. The displayed LP, rather than that name, should remain the definition used for comparison.

## Recommendation

Retain the theorem as a correct, concretely operational certification result, with the balanced-null and fresh-unit restrictions prominent. It shows how available joint access controls both sufficiency and a genuine adaptive information lower bound. It does not learn `s`, establish a common joint response law from inconsistent context data, estimate `q_r`, or learn the full joint law. Its exact source-distinct residual remains unestablished.
