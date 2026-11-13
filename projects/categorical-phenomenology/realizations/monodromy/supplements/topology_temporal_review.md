# Independent adversarial review: temporal realization and finite certification

**Supplement snapshot:** contextual research material, not exact-hash-certified against the final circle review. The final report in the package root takes precedence. See ../SOURCE_STATUS.md.

Date: 3 November 2026. Documents reviewed: `topological_native_seed.md`, especially §12, and `topology_finite.md`. This is an independent mathematical audit and a bounded primary-source search, not a novelty assessment. The earlier static audit is in `affine_independent.md`.

## Findings first

I found no counterexample to the temporal construction or the finite deterministic/smooth-randomized impossibility statements under their stated hypotheses. I checked the equations symbolically and with a separate 420-case numerical regression across all 1 ≤ r ≤ s ≤ n ≤ 7.

The important qualifications are substantive, not cosmetic:

1. The general-E temporal construction emits from the old state and then updates it. A refresh removes information from later outputs, not necessarily from the output emitted on that same step.
2. “Hold” is a nonzero contraction, not an identity transition. Memory survives every finite number of holds, but its observable signal decays geometrically. The centered preparation with only holds and refreshes produces uniform independent outputs; use a nonzero designated preparation or a kick to demonstrate memory.
3. The S² comparison is unconstrained real width 3 versus fixed-terminal normalized width 4. Signed realizations with a fixed terminal covector also need width 4. Thus this example does not isolate positivity from normalization.
4. Nonnegative temporal models must include nonnegative initial and terminal data, not merely nonnegative transition matrices, to justify reduction to nonnegative first-read factorization.
5. Deterministic finite interpolation works even with real-analytic alternatives. The randomized narrow-seam result is smooth, not analytic. With an exact-real oracle and a known analytic target, a single randomized equality query can separate that target from every fixed distinct analytic alternative almost surely.
6. The finite certificate presupposes a supplied control-domain complex and a quantitative modulus. It does not learn the base topology or certify exact algebraic rank from finitely many noisy probabilities.

The current seed already incorporates the fixed-terminal clarification. None of the checks below establishes novelty. Classical positive realization, normalized quasi-realization, fixed-matrix factorization topology, and finite noisy bundle reconstruction are direct controls.

## 1. General-E temporal equations and constants

Use the seed's notation: E is a rank-r subbundle of W=1_m-perp, n=m−1, s=g(E)≤n, and G=1⊕E. Take

    epsilon = 1/(4m),
    gamma = tau = 1/(16n²),
    Lambda = 1/(16n).

For each action a, t_a is a continuous E-section of norm at most tau and |lambda_a|≤Lambda. The unnormalized instrument is

    T_(a,y)(q,z) = (q/m + epsilon z_y,
                    (q/m + epsilon z_y)t_a + lambda_a z/m).

This is linear in (q,z), including the term epsilon z_y t_a. Its output probability at normalized state (1,z) is e_y(z)=1/m+epsilon z_y. Since z∈W,

    sum_y T_(a,y)(q,z) = (q, q t_a + lambda_a z).

For ||z||≤1, e_y(z)≥3/(4m)>0. The normalized posterior first moment is

    F_(a,y)(z) = t_a + lambda_a z / [m e_y(z)],

and satisfies

    ||F_(a,y)(z)|| ≤ 1/(16n²)+1/(12n)
                     ≤ 7/(48n) < 1/s.

All inequalities are uniform in x, a, y. Negative lambda is allowed; no positivity of lambda is used.

### Projected regular simplex

Let j_x:E_x→R^s be a fibrewise isometry. For unit regular-simplex vertices zeta_i in R^s, define

    v_i = j_x* zeta_i,
    b_i(w) = [1+s <zeta_i,j_x w>]/(s+1).

Then sum_i b_i(w)=1 and sum_i b_i(w)v_i=w. Positivity follows for ||w||<1/s. The v_i need not be the vertices of a nondegenerate s-simplex in E when s>r. This is not a defect: the construction only uses the two affine identities, not unique barycentric coordinates in E.

Define

    N_(a,y)(i,j) = e_y(v_i) b_j(F_(a,y)(v_i)).

Every entry is strictly positive. Each row sum of N_(a,y) is e_y(v_i), and summing outcomes gives row sum one. Thus the individual kernels are substochastic and their sum is stochastic. Preparation probabilities b(0) and b(gamma P a_i) are strictly positive because s gamma<1.

For any row vector rho, define its moment pair

    R(rho) = (sum_i rho_i, sum_i rho_i v_i).

Direct substitution gives the statewise, unnormalized identity

    R(rho N_(a,y)) = T_(a,y)(R(rho)).

This suffices for equality of every word probability. It also suffices for adaptive action policies: conditional action selection changes only which already-matched instrument is applied next.

### Local r+1 construction and genuine stochastic comparison

On a local orthonormal frame choose an r-simplex of radius Rloc=1/(2n). Its inradius is Rloc/r≥1/(2n²). On its containing ball,

    e_y(z) ≥ 7/(8m),
    ||F_(a,y)(z)|| ≤ 1/(16n²)+1/(28n²)
                     =11/(112n²)<1/(2n²).

The same dynamics therefore has a strictly positive local r+1-state realization. All designated preparations lie inside that simplex.

For local vertices w_i set L_ij=b_global,j(w_i). This is strictly positive and row stochastic. The identities

    N_local,(a,y) L = L N_global,(a,y),
    rho_local,i L = rho_global,i

really hold statewise, not just after outcome summation. The key identity is that

    z ↦ e_y(z) b_j(F_(a,y)(z))

is affine: if b_j(z)=b_j(0)+ell_j(z), it equals e_y(z)b_j(t_a)+(lambda_a/m)ell_j(z). Both barycentric systems preserve expectation of every affine function.

No reverse stochastic map follows. Nor may one identify local simplex frames by rotations and call those changes stochastic isomorphisms. The current one-way comparisons avoid this error.

## 2. Exact resource claims and the terminal covector

The first-read table has rows c and c+beta P a_i, with beta=epsilon gamma>0. The static theorem therefore gives pointwise native width r+1 and globally continuous labelled stochastic/nonnegative width g(E)+1. The temporal upper construction attains these bounds, so there is no additional temporal state penalty for this deliberately contracting family.

For the real comparison, embed G isometrically into a fixed carrier of rank g(G), transport preparations, instruments and terminal evaluation along the embedding, and set the instruments to zero on the orthogonal complement. The first-read table supplies the reverse bound. Thus the unrestricted continuous real minimum is g(G).

For E=TS², G is trivial of rank three, but E does not embed in a trivial rank-two bundle. Hence g(G)=3 and g(E)+1=4. In a three-dimensional trivialization, the terminal functional varies essentially as x↦xᵀ. Its kernel is the tangent-plane bundle.

A fixed terminal covector changes the comparison. If t≠0 is fixed and preparations satisfy p_i t=1, their differences lie in the fixed (k−1)-dimensional space ker(t). The same first-read difference factorization forces E to embed in that space. This argument permits signed preparations and signed kernels. Therefore fixed-terminal signed width is also g(E)+1.

Consequently the sphere establishes a normalization/terminal-structure obstruction. It would be misleading to state that “allowing negative probabilities alone reduces the global width from four to three.” It does not, if normalization means a fixed terminal functional.

A general “nonnegative realization” convention also needs nonnegative initial and terminal data. Nonnegative kernels alone do not imply a nonnegative factorization of the first-read table when the terminal evaluation may be signed. The latter is a different class.

## 3. What the memory claim proves

After summing the current output, the normalized first moment evolves by

    z ↦ t_a + lambda_a z.

For a hold with t_a=0 and lambda_a=lambda≠0, two initial moments differ after h holds by lambda^h times their original difference. Their next readout distributions differ by epsilon lambda^h times that vector. This is nonzero for every finite h, although it converges to zero.

For refresh, lambda_a=0, so the posterior moment is t_a independently of the prior state and the current outcome. With t_a=0 all later output distributions reset. However the output emitted during the refresh still has law e_y(z) from the old state. This is the emission-before-update convention.

For two kicks with common lambda, the two possible action orders differ in their translations by (1−lambda)(t_b−t_a). This is nonzero when t_a≠t_b and lambda≠1. Distinct actions with identical sections at a particular x can of course coincide at that x.

The construction does not show long-lived finite-noise memory, unrestricted invariant-cone synthesis, or arbitrary assembly of positive mechanisms. It shows exact nonzero temporal use, controlled interventions, and a sharp global resource formula for a particular strongly contracting family.

## 4. Approximation gap without a rank promise

For the first-read table H, let C=[−1_n I_n], Q have orthonormal columns spanning W, and beta=epsilon gamma. Then

    D_H=C H=beta QᵀP,
    ||C||=sqrt(m),
    D_H e=beta Qᵀe,
    D_HᵀQᵀe=beta e,  e∈E.

Suppose G=UV approximates H uniformly in operator norm by eta. No continuity or rank assumption on G itself is required below. Then ||D_G−D_H||≤sqrt(m)eta.

### Stochastic factors

If U and V are row stochastic and either one is continuous, eta<beta/sqrt(m) forces k≥g(E)+1. For continuous U, use the map e↦Pi (C U)ᵀQᵀe, where Pi projects onto 1_k-perp. Since C U 1_k=0, a kernel vector would imply D_GᵀQᵀe=0, contradicting the centered error estimate. For continuous V, e↦Pi V e is injective for the same reason. Only the selected map must be continuous.

### Nonnegative unnormalized factors

A convenient stronger-than-needed statement is: V≥0, U arbitrary real, either U or V continuous, and

    eta < beta/m

imply k≥g(E)+1.

If U is continuous use J(e)=Pi(C U)ᵀQᵀe. In its kernel, (C U)ᵀQᵀe=lambda 1_k, so D_GᵀQᵀe=lambda Vᵀ1_k lies in either the positive or negative orthant. For e∈1_m-perp, distance from beta e to either orthant is at least beta||e||/sqrt(m). But the error is at most sqrt(m)eta||e||, a contradiction.

If V is continuous put d=V1_m. The approximation excludes d=0, since G would then be zero and ||H||op≥1. The map J(e)=Pi P_(d-perp)V e is continuous. In its kernel Ve=lambda d. Because V≥0, lambda is a weighted average of the coordinates of e from any nonzero row of V, hence

    |lambda|≤sqrt((m−1)/m)||e||,
    ||e−lambda 1_m||≤sqrt(m)||e||.

Now D_G(e−lambda 1_m)=0, whereas D_H(e−lambda 1_m)=beta Qᵀe. Again the error bound gives beta||e||≤m eta||e||, impossible.

These direct arguments avoid normalization at zero rows entirely. If one instead normalizes arbitrary factors by their row sums, continuity of both original factors must be assumed to make the normalized preparation continuous; normalized decoder rows may still jump at zero. The general spectral certificate in `topology_finite.md` correctly uses that safer both-continuous statement and does not extrapolate the special projection-table bound to arbitrary spectral tables.

## 5. Finite noisy certificate audit

The finite note's proof passes the following independent checks.

- C has norm sqrt(p). Thus xi=sqrt(p)[epsilon+omega(h)] bounds centered measurement-plus-interpolation error, and q_v=(2||B_v||+xi)xi bounds covariance error.
- The separation q_v<gamma_v/4 gives actual spectral gap at least gamma_v−2q_v>0 and projector error below 1/3 via q_v/(gamma_v−q_v).
- On an edge, neighboring projectors differ by less than 2/3, so sigma_min(Q_vᵀQ_w)>sqrt(5)/3. The actual transition matrix differs from Q_vᵀQ_w by less than 1/3. Their determinant signs agree. This is enough to prove exact triangle consistency, not merely a heuristic eigenvector alignment.
- The top-r spectral bundle lies in 1_m-perp because the rth eigenvalue is positive and B1_m=0. Smaller singular values may appear or disappear without affecting the construction.
- The robust normalized factor obstruction follows by invertibility of P_F B'|E. Either preparation or readout continuity suffices, with no candidate-rank promise.
- The signal bound min_v sqrt(lambda_r(G_v)−q_v) is positive and valid over every star. The sample-fit/modulus inequalities follow by the triangle inequality.
- The data-only barycentric interpolant is a useful separate theorem. A candidate modulus plus finite agreement can exclude candidates near that interpolant without assuming a modulus for the unknown truth. To identify its bundle with the truth's bundle, one does need the extra truth control.
- The Hoeffding/union-bound sample inequality is conservative but valid, using entrywise errors followed by a Frobenius bound on the operator norm.
- A rank-one cup-power witness gives the asserted complement-bundle lower bound. Nonorientability alone supplies only the first increment. TS² has w_1=w_2=0 and needs an Euler-class or equivalent nontriviality witness; the finite note does not falsely apply w_1 to it.

Technical presentation cleanup: define a maximum over an isolated vertex's empty neighbor set as zero, or include the vertex itself in that maximum. Standard measurability of randomized algorithms and padding of their post-halting query sequence can be made explicit in the no-go proof.

## 6. Deterministic and randomized no-go checks

### Deterministic finite exact interpolation

For distinct sampled parameters x_1,...,x_N, let

    q_i(x)=product_(j≠i) d(x,x_j)^2,
    w_i(x)=q_i(x)/sum_j q_j(x).

The denominator is positive everywhere. These weights are nonnegative, sum to one, and interpolate Kronecker data. Convexly interpolating separately chosen small stochastic factors U_i,V_i therefore gives continuous factors agreeing at every sample. The interpolated product need not agree between samples, which is precisely the point.

On a real-analytic embedded manifold, squared ambient distances make the weights real analytic, because their common denominator never vanishes. The projective embedding [u]↦uuᵀ supplies this for RP^d. Repeated query points are first deduplicated.

For deterministic adaptive sampling, run the target first, then construct the alternative for the resulting finite query set. Induction shows that the alternative produces the same answers, hence the same adaptive query path and output. This is a nonuniform indistinguishability statement, not a single alternative defeating all possible query paths.

Interpolating whole preparation/instrument arrays gives exact equality of every controlled horizon at each sampled parameter. Finite time experiments at fixed parameters therefore do not rescue finite identification.

### Smooth randomized narrow seam

For RP^d, d≥1, unit v and cutoff f that vanishes on a neighborhood of zero and equals one on [eta,1], set t=v·u and

    z_v([u])=f(|t|)sign(t)u+[1−f(|t|)]v.

The formula is antipodally invariant. It is smooth at t=0 because the first term vanishes in a neighborhood. It never vanishes because

    z_v·v=f(|t|)|t|+1−f(|t|)>0.

Also ||z_v||≤1. Using z_v instead of a chosen sign of u gives a global smooth two-state alternative with constant centered rank one, matching the target outside the band |v·u|<eta.

For uniform random v, every fixed u has band probability p_d(eta)=O_d(eta), independently of u. For d=1 this is 2 arcsin(eta)/pi. Fix a randomized algorithm that makes finitely many queries almost surely on the target. Choose N so its target tail probability is below epsilon/2 and eta so N p_d(eta)<epsilon/2. The target query path is independent of the randomly selected seam. A union bound and averaging yield a fixed v with probability of a target-band hit before stopping below epsilon. Couple target and alternative until that hit: all preceding exact responses and action laws agree. The full transcript laws are within epsilon in total variation. Possible failure to halt on the bad event does not invalidate the coupling if infinite transcripts are included in the transcript space.

This establishes lack of uniform two-sided testing guarantees for the smooth alternative class. It does not show that one fixed alternative defeats every algorithm, or that every alternative is hard.

### Explicit analytic counterexample to an overextension

Suppose the target response is a known real-analytic matrix function on a connected analytic parameter manifold. Each fixed analytic small-state alternative differs from the target in at least one entry, since global equality is topologically impossible. The zero set of that nonzero analytic difference has measure zero. Querying at one absolutely continuously random point and testing exact equality distinguishes the target from that fixed alternative almost surely. The same equality test works pointwise for every fixed alternative. Thus the randomized theorem cannot be extended from smooth to analytic candidates in this exact-real oracle model merely by invoking deterministic analytic interpolation.

This does not contradict the smooth theorem: a smooth cutoff can equal the target on an open set, while a distinct analytic response cannot. Finite-precision/noisy analytic testing would be a different problem.

The seam argument applies to the sign/projective controlled family used in the finite note. It has not been proved here for every general-E temporal construction. Likewise, changing the parameter during one latent-state trajectory is a different oracle unless a cross-parameter transport mechanism has been specified.

## 7. Independent numerical regression

Files: `topology_temporal_review_checks.py` and `topology_temporal_review_checks.json`.

The separate script tested 420 random subspaces/isometric embeddings over all 1≤r≤s≤n≤7, with random admissible actions, local/global simplices, and ten-step words. Maximum residuals were:

- local-global instrument intertwining: 5.56×10^−17;
- moment intertwining: 4.08×10^−17;
- controlled word probabilities: 1.12×10^−16;
- stochastic normalization: 2.23×10^−16;
- preparation comparison: 1.12×10^−16;
- memory update: 1.26×10^−16.

The smallest tested kernel entry was 0.01148. These are implementation checks, not proofs of topology or evidence of novelty.

## 8. Primary-source comparison: exactly what was checked

### Direct normalized stochastic and temporal precedents

**Mond, Smith and van Straten (2003), “Stochastic factorizations, sandwiched simplices and the topology of the space of explanations.”** Primary author PDF checked, including the stochastic-factor/sandwiched-simplex correspondence and regular-simplex deformation arguments. This is a direct precedent for normalized factor geometry and nontrivial factorization-space topology. Its fixed-table solution space is not itself a theorem about minimal globally continuous factor width over an external parameter bundle. That distinction does not establish novelty. [DOI](https://doi.org/10.1098/rspa.2003.1150), [author PDF](https://download.uni-mainz.de/mathematik/Algebraische%20Geometrie/DvS-Publikationen/30.Stochastic%20factorizations,%20sandwiched%20simplices%20and%20the%20topology%20of%20the%20space%20of%20explanations%20-%202003.pdf).

**Vidyasagar (2011), “The complete realization problem for hidden Markov models: a survey and some new results.”** The author-uploaded full text was checked in the stable-polyhedral-set and cone-construction sections; the published DOI was verified. The construction uses cone generators Y and nonnegative matrices satisfying D(u)Y=YG(u), together with nonnegative initial/terminal data, then converts to stochastic form. This is direct prior art for the temporal native realization mechanism. The inspected statements concern a single process rather than a continuously parameterized bundle or the formula g(E)+1. [Published article](https://link.springer.com/article/10.1007/s00498-011-0066-7), [author-uploaded full text](https://www.researchgate.net/publication/220210303_The_complete_realization_problem_for_hidden_Markov_models_A_survey_and_some_new_results).

**Monràs and Winter (2016), “Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem.”** Full primary text checked in Definitions 1 and 5, Theorem 6, and §4. Definition 5 fixes the terminal vector to all ones; Theorem 6 states a stable polyhedral-cone criterion; §4 treats minimal and quotient realizations. This is particularly close to the fixed-terminal/quasi-real distinction in the seed. The inspected results do not discuss an external parameter bundle. [Primary text](https://arxiv.org/html/1412.3634), [DOI](https://doi.org/10.1063/1.4936935).

**Anderson (1999), “The realization problem for hidden Markov models.”** Primary institutional abstract checked, not the full forty-page paper. It directly concerns finite output-string laws and polyhedral-cone realization. It should remain a central antecedent, but no exact theorem comparison beyond the accessible material is claimed here. [Primary institutional record](https://researchportalplus.anu.edu.au/en/publications/realization-problem-for-hidden-markov-models/), [DOI](https://doi.org/10.1007/PL00009846).

**Barreto, Precup and Pineau (2016), “Practical Kernel-Based Reinforcement Learning.”** Primary JMLR text checked in §§2–3 and relevant continuity statements. It uses normalized stochastic factors and factor swapping to build smaller transition models for continuous-state control. Its continuum is the state/control approximation domain; the inspected results do not give a topological external-family width obstruction. [Primary PDF](https://jmlr.org/papers/volume17/13-134/13-134.pdf).

### Continuous factor correspondence, local positivity, and fixed-fibre topology

**Ke, Montiel Olea and Nesbit (2024), supplement to “Robust machine learning algorithms for text analysis.”** Appendix A was checked. It explicitly studies continuity of the correspondence of exact column-stochastic NMFs and extremal continuous functionals over those factors. A continuous set-valued correspondence is not a global continuous single-valued selection. I did not audit every hypothesis in its boundary argument, and do not use it to prove the seed. [Primary supplement](https://www.econometricsociety.org/publications/quantitative-economics/2024/11/01/Robust-Machine-Learning-Algorithms-for-Text-Analysis/supp/quan200329-sup-0001-onlineappendix.pdf).

**Krone and Kubjas (2021), “Uniqueness of nonnegative matrix factorizations by rigidity theory.”** Primary full text checked in the introduction, relevant geometry, and Proposition 5.3. It connects strictly positive rank factorizations with interior points of the fixed-rank nonnegative-rank locus and studies rigidity and factorization-space boundaries. It follows and cites Mond. This supplies a concrete local positive-factor precedent, not the global bundle formula. [Primary PDF](https://arxiv.org/pdf/1902.02868), [DOI](https://doi.org/10.1137/19M1279472).

**Hrubeš (2020), “On epsilon-sensitive monotone computations.”** Lemma 3.9 and neighboring sections were checked previously: adding a sufficiently large positive rank-one baseline gives a rank-plus-one nonnegative factorization. This is a direct pointwise construction precedent. Continuity/rank behavior there is not the external-family section problem addressed here. [Author PDF](https://users.math.cas.cz/~hrubes/PDFs/Epsilon.pdf), [DOI](https://doi.org/10.1007/s00037-020-00196-6).

**Shitov, “A universality theorem for nonnegative matrix factorizations,” and Dobbins–Holmsen–Miltzow, “A Universality Theorem for Nested Polytopes.”** Primary texts checked previously. They establish very broad fixed-instance solution-space complexity, including normalized/permutation quotients. They block any broad claim that factorization spaces have simple topology. I found no external continuous-family embedding-width statement in the inspected versions. [Shitov](https://arxiv.org/abs/1606.09068), [nested polytopes](https://arxiv.org/abs/1908.02213).

### Relevant-looking titles that do not establish the desired result

**Krylov (2008), “On factorizations of smooth nonnegative matrix-values functions and on smooth functions with values in polyhedra.”** The primary paper's opening sections and polyhedral-coordinate statement were inspected. “Nonnegative” there means positive semidefinite symmetric matrix values, with sums of fixed-direction rank-one PSD forms, not entrywise stochastic NMF of minimal width. Smooth positive barycentric coordinates inside a fixed polyhedron are relevant to upper constructions but do not settle the bundle obstruction. [Primary PDF](https://arxiv.org/pdf/0706.0192), [DOI](https://doi.org/10.1007/s00245-008-9040-2).

**Hazewinkel, “A partial survey of the uses of algebraic geometry in systems and control theory.”** Primary report checked in its families-over-a-base and realization-with-parameters discussion. It explicitly models continuously parameterized systems by vector bundles. This is a strong antecedent for the unconstrained real part, but the searched material was not a normalized/nonnegative theorem. [Primary report](https://ir.cwi.nl/pub/10385/10385D.pdf).

**Vechtomov, Mikhalev and Sidorov, “Semirings of continuous functions.”** The primary MathNet full-text route failed, but an author-uploaded full text was subsequently located and searched. The inspected projectivity results concern ideals of C(X)_+, including pure and prime ideals. Full-text searches found no factorization or bundle discussion and only an unrelated reference containing “matrix.” This closes the most obvious semiring lead in this source; it does not exclude relevant semimodule literature elsewhere. [Author-uploaded text](https://www.researchgate.net/publication/330425232_Semirings_of_Continuous_Functions), [DOI](https://doi.org/10.1007/s10958-019-4150-8).

**Scoccola and Perea (2023), “Approximate and discrete Euclidean vector bundles.”** Primary text checked at Theorem 5.15, Proposition 6.8 and the neighboring Euler-class algorithm. It gives finite noisy bundle reconstruction, stable characteristic-class computation, and explicit simplicial procedures. These are direct antecedents for the finite note, which should be presented as an interface from response tables to normalized latent-state bounds rather than as a new way to reconstruct bundles or compute characteristic classes. [Primary PDF](https://arxiv.org/pdf/2104.07563), [DOI](https://doi.org/10.1017/fms.2023.16).

Searches also covered combinations of continuous families, nonnegative matrices over C(X), continuous mixtures, normalized affine realizations, terminal covectors, continuous nested-simplex selection, and citation trails around Mond, Hazewinkel, Hrubeš, and Shitov. Many hits concerned continuous-time dynamics, PSD factorizations, fixed-matrix topology, signal-index factorization, or unrelated uses of “matrix factorization.” No exact matching theorem was located in this pass. That last sentence records the search outcome only; it is not a claim that no such theorem exists.

## Final assessment

The current construction and finite results survive this audit. Their defensible presentation is an explicit, sharply typed synthesis with complete constants and operational scope. The sphere gap must retain the varying-versus-fixed terminal qualification; the randomized no-go must retain the smooth-versus-analytic distinction; and classical normalized positive-realization theory must be treated as a direct comparator. No novelty conclusion is warranted by this review.
