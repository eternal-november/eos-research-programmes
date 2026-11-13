# Adversarial audit: robust local purification conversion

Date: 2026-11-05. Auditor: independent task worker. Target: `unfamiliar_purification_20261105/robust_local_purification_conversion.tex`, as read at 16:17 UTC. No candidate check script was imported or used.

## Verdict

The stated **constant-error obstruction to bounded backward locality radius is mathematically sound**, subject to making the tensor orientation explicit. I found no substantive gap in the normalized equal-state purification, exact conversion, prime-size covariance, causal-cone separation, error conversion, or pure product-ancilla argument.

This is **not** a proof of the more permissive arbitrary size-/site-dependent bounded-bond MPU assertion, and the draft correctly disclaims that conclusion. Historical originality is **not established**. The ingredients and framework are existing literature; the particular constant-multiplicity witness and explicit robustness estimate were not found in the cited sources or a small targeted search. That negative search is weak novelty evidence, not certification.

## Small corrections / clarifications

1. **Shift orientation:** Under ordinary contraction `tr(W^{i_1 a_1} ... W^{i_N a_N})` and the draft's vectorization convention (i is input/reference, a is environment/output), `W^{ia}_{alpha beta}=delta_{i alpha}delta_{a beta}` imposes `a_j=i_{j+1}`. It generates the **left** shift, not the specified right shift. For right shift use `W^{ia}_{alpha beta}=delta_{a alpha}delta_{i beta}`. Alternatively explicitly reverse contraction order. Merely allowing an unspecified 'opposite orientation' is avoidably ambiguous. This is a convention issue, not an obstruction to the construction; swapping shift direction or transposing W repairs it completely. The source paper uses a different matrix/vectorization orientation, so copying its W without reconciling that orientation causes the discrepancy.
2. **Normalization:** Say the fixed tensor generates the *unnormalized* purification, and apply its displayed global normalization afterward. Normalized states still have bond at most 5, but their normalization scalar depends on N. This is standard and does not weaken the theorem.
3. **Ancilla wording:** Make 'pure product input and specified pure product target' explicit at the theorem statement, rather than relying on later clarification. Mixed product inputs still satisfy the covariance lemma but are not directly covered by the stated pure vector error.
4. **Uniform MPU qualification:** 'Fixed homogeneous periodic MPU family' should mean one tensor, independent of N, whose periodic contraction is exactly unitary for all sizes. The cited QCA theorem cannot be applied merely because a tensor is homogeneous at one selected size. The present text appears to intend the correct stronger hypothesis.

## Detailed checks

### Supplied states and finite tensors

Let D=2^N. For right-shift permutation S, both A=I+2S and B=A† are normal and invertible. Their singular values are |1+2z| with z on the unit circle, hence in [1,3]. We have A†A=B†B=5I+2(S+S^-1), and `||A||_F^2=||B||_F^2=5D+8`, since tr(S)=tr(S^-1)=2. The physical marginal of `sum_x |x> M|x>` is `(M†M)^T`, not MM†, but equality holds exactly. Indeed the common marginal here is `(5I+2S+2S^-1)/(5D+8)`.

With the orientation correction above, the homogeneous periodic local tensor `diag(delta_{ia},W^{ia},W^{ia})` has virtual dimension 1+2+2=5. A product of block diagonal matrices remains block diagonal, and tracing sums the sector contributions, giving I+S+S. The coefficient is exactly 2 for every N. It does **not** become 2^N. The local physical and environment dimensions are both 2, and all unnormalized tensor entries are rational. Exchanging physical/environment indices gives the adjoint purification. This really is a fixed finite LPDO purification representation.

The tensor is reducible and not an injective MPS tensor after any blocking; products remain in its block diagonal subalgebra with duplicated sectors. The theorem must not be advertised as a result for injective or deterministically shallow-prepared purifications. The draft does not do so.

### Exact environment converter

B is invertible. Thus VB=A uniquely forces V=U=AB^-1. Since A†A=B†B, U†U=I. Allowing equality of pure-state rays adds only a scalar phase. No hidden kernel freedom is available.

### Cyclic-group coefficients

The shift's one-excitation subspace contains every Nth root of unity, so expanding U as `sum_{k=0}^{N-1}u_k S^k` gives uniquely determined coefficients. Scalar unitarity at each root and Fourier Parseval give `sum |u_k|^2=1`. Evaluation at z=1 gives `sum u_k=1`.

An independent way to compute the coefficients is the cyclic linear system `u_k+2u_{k+1}=delta_{k0}+2delta_{k1}`, which comes directly from UB=A. Solving it in rational arithmetic reproduces the claimed `u_1=(2^{N-1}+2)/(2^N+1)` for odd N. The inverse geometric expansion in the draft has the correct sign and starting power.

### Choi covariance

In the k=k' term, Q_j is the product of independent signs at indices j and j+1-k, so it has expectation one only at k=1. For Q_jQ_l, repeated signs can pair directly (k=1) or crosswise. Crosswise pairing would require `2(k-1)=0 mod N`; odd N makes that impossible unless k=1, contradicting distinct j,l in that alternative. This diagonal part does not itself need primality.

For k!=k', prime N implies fixed strings of `S^{k-k'}` are exactly the two constant strings. On both, Q_j and Q_jQ_l equal +1. Every off-diagonal element is therefore 2/D, independent of k,k', and the sum of these terms cancels because `|sum u_k|^2-sum |u_k|^2=0`. Thus both one-point moments and the two-point moment equal p=|u_1|^2. The covariance is p(1-p), with p in [1/4,4/9], giving at least 3/16.

Primality is genuinely used. The exact formula fails at the composite test size N=9; it must not be silently generalized to all odd sizes.

### Locality and quantifiers

The initial Choi input is a product over lattice sites of physical/environment Bell pairs. Under a backward-radius-R environment unitary, Q_j pulls back to a set contained in the circular radius-(R+1) neighborhood of j. If the circular distance between j and l exceeds 2R+2, the pulled-back observables act on disjoint factors of that product input, so their covariance vanishes exactly. Translation invariance is unnecessary, and only backward locality is used. Pure on-site auxiliary input factors preserve this argument regardless of their finite dimensions.

For prime odd N choose distance (N-1)/2. The sufficient inequality is exactly R<(N-5)/4. For N=3,5 this is vacuous for nonnegative radii, which is harmless. If e_N<1/96 then R>=(N-5)/4 on each applicable prime size. Infinitely many primes therefore refute any radius bound independent of N. Radius may depend on the chosen accuracy; every finite bound still fails for sufficiently large primes. Depth t with gate diameter at most ell implies backward radius at most t*ell, so the corresponding circuit statement follows under that gate model.

### Norms and constants

For unit pure states at phase-adjusted Euclidean distance Delta, norm-one observable expectations differ by at most 2Delta. The connected covariance difference is bounded by 2Delta for Q_jQ_l plus 4Delta for the product of one-point functions, hence at most 6Delta. A covariance gap 3/16 therefore forces Delta>=1/32.

Right multiplication by B has minimum singular value at least 1 in Frobenius norm, and `||B||_F<=3sqrt(D)`. Consequently normalized conversion error is at least one third the normalized Frobenius converter error. This gives 1/96 exactly as stated. Global phases cause no problem because the estimates hold phasewise. The bound is conservative, not optimized.

For pure states, with c=|<psi|phi>|, e^2=2(1-c) and trace distance squared is 1-c^2=e^2(1+c)/2. Thus T>=e/sqrt(2) and the draft's trace-distance corollary is valid.

### Auxiliaries / catalysts

Take the reference-state target `|U>>/sqrt(D) tensor |a_out>` and the enlarged local converter acting on Bell input and `|a_in>`. Q observables ignore auxiliaries, so the target covariance stays nonzero and the converter covariance is zero. Applying B^T to the untouched physical/reference register transforms these into the supplied-purification target and actual output, with common factor sqrt(D)/||B||_F. The least singular value of B^T is still at least 1, giving the same factor-one-third bound.

This does not require a locality claim about B^T; B^T is only a mathematical norm comparison. Initially entangled or classically correlated auxiliaries are outside the product-input proof. Postselection, unrestricted feed-forward, long sequential sweeps, and arbitrary discard/mixed-output metrics are also not proved covered. The draft appropriately excludes them. These are real scope restrictions, not cosmetic caveats.

## Literature overlap and scope

- [Yauk–Liu–Cirac, §V.1](https://arxiv.org/html/2608.02724v1#S5.SS1): Their normal A/B† construction, shift-polynomial inverse, and exact operator-Schmidt obstruction are direct antecedents. They explicitly observe that the epsilon^N example trivializes thermodynamically and handle the modulus-one case by a phase times a shift. Therefore the draft's diagnosis of this limitation is not itself new. Their construction uses a weighted sector; the present duplicated sector keeps its relative weight constant. I did not find the present robust covariance estimate in that section or the discussion.
- [Cirac et al., §III and Appendix A](https://arxiv.org/html/1703.09188v2): Their definition uses a fixed periodic tensor producing unitaries at every size; the structure theorem yields a strict causal cone. This supports the narrowly qualified uniform-MPU consequence.
- [Styliaris et al., introduction and §III](https://arxiv.org/html/2406.10195v2): They explicitly distinguish arbitrary-boundary/nonuniform MPU from fixed periodic uniform families, and exhibit nonlocal bounded-bond MPU capable of long-range correlations. This supports the warning that covariance obstruction alone says nothing against all bounded-bond MPU.

The original epsilon^N family really does have simple fixed-error converters for sufficiently large N: identity for |epsilon|<1 and a phase times S^2 for |epsilon|>1, with the stated geometric error bounds; at modulus one a phase times S converts exactly. Treating finitely many remaining sizes individually gives a bounded bond bound for the broad size-dependent approximation question. This does not make the resulting family a single homogeneous periodic MPU tensor and should not be read as such.

No arbitrary bounded-bond unitary lower bound follows from a long-range covariance witness. A bounded-bond *linear* truncation of U's shift series likewise does not settle that broader question, because exact unitarity may be lost. The draft handles these distinctions correctly.

## Reproducible artifacts

- `check_independent.py`: self-contained independent script, exact Fraction arithmetic plus NumPy dense checks.
- `results.json`: successful output.
- Exact moments tested for prime sizes 3,5,7,11,13; composite 9 is an intentional negative control.
- Dense equal-marginal/unitarity/conversion/norm checks at 3,5,7, with numerical deviations at most about 2.3e-16.
- Explicit local tensor contractions at 3 and 4 confirm the orientation discrepancy and verify the corrected bond-5 tensor with zero mismatches.

Run with `OPENBLAS_NUM_THREADS=1 python check_independent.py`.

## Addendum: revisions and stronger mixed-output result (16:29 UTC)

The author worker corrected the W orientation and explicitly added the supplied-state long-range order. I independently verified the added statement: for every N>=3 and distinct sites, the Q_j and Q_jQ_l moments of |a_N> equal `(4D+8)/(5D+8)`, so their connected covariance tends to 4/25. The identity diagonal contribution is zero, the shift diagonal contribution is 4D, and the two interference terms total 8. No prime hypothesis is required for this supplied-state computation because the only off-diagonal relative shift is one step.

**Important injectivity distinction:** The earlier caution in this audit means ordinary MPS injectivity, not step-injectivity. The corrected local T_A, viewed as `(a,beta) -> (i,alpha)`, is exactly `I_2 direct-sum SWAP direct-sum SWAP` and is step-injective according to Yauk–Liu–Cirac Definition 6. T_B need not be. Their Theorem III.2 compares sequential LPDO states with the final memory retained; equality after periodic closure does not imply equality of those sequential states. Its MPI conclusion also must not be replaced by a causal-radius conclusion. This reconciles the witness with their positive theorem.

**Verified strengthening:** The original no-discard scope restriction is unnecessary if the error is measured in trace distance and locality is imposed on a product-ancilla unitary dilation. Let Lambda be a channel obtained by a backward-radius-R unitary acting on E and arbitrary finite-dimensional, initially product local auxiliary states, with arbitrary auxiliaries discarded at the end. Set sigma=(Id tensor Lambda)(|b><b|) and tau=|a><a|. Let J_Lambda be Lambda's normalized Choi state and J_U=|chi_U><chi_U|.

Write K=B^{-T} on the reference, identity on all other factors. Commutation of reference filtering with Lambda and the vectorization identity give exactly

`J_Lambda-J_U = (||B||_F^2/D) (K tensor I)(sigma-tau)(K† tensor I)`.

Both Choi matrices are normalized. Trace-norm submultiplicativity gives

`T(J_Lambda,J_U) <= (5+8/D) ||B^-1||_op^2 T(sigma,tau) <= 6 T(sigma,tau)` for N>=3.

A product local dilation still has zero distant Q covariance after discarding its auxiliaries, because all these moments can be computed before the discard. The target Choi covariance is at least 3/16 at prime sizes. For mixed states, connected covariance changes by at most 6 times trace distance, using `|Tr(O(rho-sigma))| <= 2T` for norm-one O. Thus the same separation condition R<(N-5)/4 forces

`T(J_Lambda,J_U)>=1/32`, hence `T(sigma,tau)>=1/192`.

This extension permits arbitrary discarded output, even mixed product ancillary input. It still excludes initially correlated auxiliary resources, postselection, and unbounded classical communication. A generic no-signalling or causal channel need not admit the stipulated product local dilation, so the locality hypothesis must remain on the implementing unitary dilation, not merely on the reduced channel.

The additional independent script `check_channel_filter.py` uses a product amplitude-damping channel and confirms the inverse-filter equality to 2.8e-17 and the trace-norm comparison. Output is `channel_results.json`. Its N=3 run checks the algebra only, since the spatial lower-bound condition is vacuous at that size.
