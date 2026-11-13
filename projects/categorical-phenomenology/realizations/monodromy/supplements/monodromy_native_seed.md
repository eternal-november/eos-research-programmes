# A cone obstruction invisible to the observable vector bundle

**Supplement snapshot:** contextual research material, not exact-hash-certified against the final circle review. The final report in the package root takes precedence. See ../SOURCE_STATUS.md.

**Research note, 3 November 2026.** A derived, independently auditable example, not a novelty claim. It separates continuous positive realization from continuous signed realization while keeping the terminal functional fixed. Unlike the tangent-sphere normalization example, its observable vector bundle is explicitly trivial. The obstruction is the nontrivial covering of identifiable extreme predictive states. Mixture label switching, realization by invariant cones, and covering-space monodromy are classical; source comparison remains essential.

## 1. Exact native semantics and statement

A k-state stochastic realization consists of a row probability vector ρ(x), continuous nonnegative k×k matrices N_y(x) for the fixed output alphabet Y={1,2,3}, and the fixed terminal column 1_k. The sum Σ_yN_y is row stochastic. The probability of a finite output word w=y_1…y_l is ρN_{y_1}…N_{y_l}1_k. States have fixed global labels; all matrices are continuous on the base circle. The external parameter is fixed throughout each experimental word. No cross-parameter state transport law is part of the input or claimed by the realization. An ordinary signed normalized realization permits signed entries but keeps the same fixed terminal 1_k, normalized initial row, and (Σ_yN_y)1_k=1_k.

There exists a real-analytic family of output laws over S¹ such that:

- every individual law has minimal stochastic size three;
- a globally continuous normalized signed three-state realization exists, with a fixed initial uniform distribution and fixed terminal 1_3;
- no globally continuous stochastic three-state realization exists;
- a globally continuous, and indeed smooth, stochastic four-state realization exists;
- the full rank-three observable response bundle and its centered rank-two subbundle are trivial. The one-symbol-prefix/suffix Hankel block is even constant and invertible.

Thus the global positive width is four whereas the global normalized signed width is three. The centered-bundle bound g(E)+1 is three and is not complete for this temporal family. Nonnegative kernels in the four-state construction have zeros; strict positivity is not claimed. The hidden process retains a chosen latent component indefinitely.

## 2. A rotating unordered emission triangle

Represent the parameter circle as t∈[0,1] with endpoints identified. Put

    c=(1,1,1)/3,
    a=(1,−1,0)/√2,
    b=(1,1,−2)/√6,
    θ(t)=2πt/3,
    0<δ<1/3.

For i=1,2,3 define local emission rows

    v_i(t)=c+δ[cos(θ(t)+2π(i−1)/3)a
                    +sin(θ(t)+2π(i−1)/3)b].              (1)

Let V(t) have rows v_i(t), let π=(1,1,1)/3, and let M_y(t)=diag(V(t)[:,y]). All v_i are strictly positive probability vectors. Each M_y is nonnegative and Σ_yM_y=I_3. The local model selects one latent component uniformly and repeatedly emits independently from that component, without changing it.

Let P be the permutation matrix with rows e_2,e_3,e_1. Then

    V(1)=PV(0),  M_y(1)=PM_y(0)P^−1,  πP=π.

Consequently

    p_t(w)=(1/3)Σ_i ∏_{j=1}^l v_i(t)_{y_j}               (2)

is periodic and defines a law over the parameter circle. It is real analytic: extending θ to all real t, every word function is analytic and 1-periodic. Public outputs retain their fixed labels; only the hidden mixture labels cycle.

## 3. Reachability, observability, and a constant Hankel block

The rows of V are affinely independent, and V is invertible. For the prefixes and suffixes consisting of one symbol, the reachability and observability matrices are

    R=V^T/3,       O=V.

Their product is the observable length-two Hankel block

    H_ab=p_t(ab)=(V^TV)_ab/3.

The regular-triangle identity gives

    V^TV = (1/3)11^T+(3δ²/2)(aa^T+bb^T),                 (3)

independent of t and positive definite. Thus the Hankel rank is at least three and at most three from the displayed realization. Both reachability and observability have full dimension three. No generic mixture-identifiability theorem or de Finetti argument is needed.

The fixed invertible block provides a global frame for the full response space. Its centered subspace has rank two and is also fixed: the constant normalization direction splits off. This verifies triviality directly. Third-order moments, rather than the constant second-order block, carry the rotating extreme-state configuration.

## 4. Why three continuous positive states are impossible

Suppose, at one parameter, a three-state stochastic model (ρ,N_y,1_3) generates the same all-word law. Form its one-symbol R′ and O′. Since R′O′=H and H is invertible, both R′ and O′ are invertible. There is an invertible S with

    R′=RS,      O′=S^−1O.

Equality of the length-three blocks gives

    R M_y O = R′N_yO′,
    M_y = S N_y S^−1.

Summing over y yields Σ_yN_y=I_3. Every off-diagonal entry of every N_y is nonnegative, and its sum over y is zero. Hence every N_y is diagonal.

The joint diagonal tuples (N_1(j,j),N_2(j,j),N_3(j,j)) must therefore equal the three distinct rows v_i, up to a permutation. To see this without choosing one output with accidental repeated eigenvalues, use the common eigenspaces of all three diagonal M_y: the distinct emission tuples make these exactly the three coordinate lines. Similarity preserves that joint spectrum.

If the N_y varied continuously on the parameter circle, their diagonal tuples would continuously enumerate the three points {v_1(t),v_2(t),v_3(t)}. On the interval, a chosen tuple must follow one branch v_i(t), because the branches never collide. After one loop that branch becomes v_{i+1}(0), not v_i(0), contradicting periodicity. Thus no continuous three-state positive realization exists. Continuity of the initial row is not needed for this lower bound; continuity of the outcome kernels is enough.

Only word lengths two and three are used to force the lower bound. The upper constructions nevertheless reproduce every finite word.

## 5. A global signed realization with fixed normalization

Put V_0=V(0) and

    S(t)=V(t)V_0^−1.

It satisfies S(0)=I, S(1)=P, S(t)1=1, and πS(t)=π. In fact it is an orthogonal path fixing the normalization direction, because the rows form a rotating regular triangle. Define

    N_y^signed(t)=S(t)^−1 M_y(t) S(t).                    (4)

Then N_y^signed(1)=N_y^signed(0), Σ_yN_y^signed=I, and πN_{y_1}^signed…N_{y_l}^signed1=p_t(w). Periodicity holds for all derivatives, so this realization is analytic on S¹. The initial vector π and terminal vector 1 are fixed. Some kernel entries must become negative, by the preceding impossibility theorem.

This is a positivity obstruction, not the varying-terminal artifact in the tangent-sphere example.

## 6. A four-state positive lift with one spare label

Use four globally labelled native slots and three local component labels A,B,C. At t=0 take

    Q_0=[e_1; e_2; e_3]          (three rows, four columns),
    L_0=[e_A; e_B; e_C; u]       (four rows, three columns),
    u=(1,1,1)/3.

We construct row-stochastic Q(t),L(t) with Q(t)L(t)=I_3. Whenever a row of Q assigns positive probability to a slot, the corresponding row of L must be that component's unit vector. An empty slot is free to change its L row continuously.

Divide [0,1] into nine equal stages. Interpolate the stated single row convexly, leaving all other rows fixed:

1. Recolor empty slot 4: L_4 goes from u to e_A.
2. Move component A: Q_A goes from e_1 to e_4.
3. Recolor now-empty slot 1: L_1 goes from e_A to e_C.
4. Move component C: Q_C goes from e_3 to e_1.
5. Recolor now-empty slot 3: L_3 goes from e_C to e_B.
6. Move component B: Q_B goes from e_2 to e_3.
7. Recolor now-empty slot 2: L_2 goes from e_B to e_A.
8. Move component A: Q_A goes from e_4 to e_2.
9. Recolor now-empty slot 4: L_4 goes from e_A to u.

During every move, the source and destination slots have the same unit decoder row. During every recolor, its slot is absent from the support of every Q row. Thus QL=I holds throughout. At the end,

    Q_1=PQ_0,       L_1=L_0P^−1.

Now set

    X_y(t)=L(t)M_y(t)Q(t),       ρ(t)=πQ(t).              (5)

These are nonnegative and row normalized after summing outcomes. The endpoint equations make X_y and ρ periodic. Since QL=I,

    X_y L=LM_y,       ρL=π,

and telescoping proves equality of every finite-word law. Hence four globally labelled states suffice and the lower bound makes four optimal.

Piecewise linear interpolation gives continuity. For smoothness, replace the stage coordinate by a C∞ step function that is flat at both endpoints. Every Q,L jet at the interval endpoints is constant, and the local M jets transform by P. Therefore the descended X_y,ρ are C∞ on the circle. This support-based construction is not analytic; no analytic four-state lift is asserted.

### Exact ordinary state-emitting form and controls

The lift is an ordinary state-emitting HMM in the transition-then-emission convention, not merely a general outcome-labelled transition system. Put

    T=LQ,        E=LV.

Because a Q row is supported only on slots whose decoder is its component unit vector,

    Q diag(E[:,y])=diag(V[:,y])Q,
    T diag(E[:,y])=X_y.

These equations hold for all native slots, including the temporarily empty spare. E is strictly positive; T has structural zeros. In the emission-before-transition convention, the equivalent model agrees on the reachable occupied slots.

The public interface can additionally contain hold, cycle, and refresh. Let T_hold=I_3, T_cycle=P, and T_refresh=11^T/3, acting before emission, and set M_{a,y}=T_a diag(V[:,y]). All T_a commute with monodromy P, so these labelled action/outcome laws descend. Their global transition matrices are L T_a Q with the same emission matrix E, and their outcome kernels are L M_{a,y}Q. The same statewise retention and all-word calculation applies, including adaptive public action choices. The hold subexperiment already forces the lower bound. Refresh removes persistence; cycle changes which component emits. These are genuine interventions on a fixed-parameter native mechanism.

### A uniform finite-moment robustness statement

There exists κ>0 such that no continuous three-state stochastic model family can approximate all target word probabilities of lengths at most three uniformly over the parameter circle to error less than κ. No rank condition or uniform modulus is imposed on the competitor. This statement concerns uniform coverage of the continuum, not finitely sampled parameter locations.

Here is a compactness proof. The space Z of three-state stochastic parameters (ρ,N_1,N_2,N_3) is compact: all coordinates are nonnegative and each row of Σ_yN_y sums to one. Let F_t⊂Z be the exact fiber for word lengths at most three. The proof above gives Σ_yN_y=I and a simultaneous permutation of the three emission tuples. Matching H then forces ρ=(1/3,1/3,1/3). Thus F_t consists of exactly six permuted diagonal models. These are uniformly separated in Z and vary as a nontrivial finite covering of S¹.

Choose η smaller than one third of the minimum separation between different elements of the same F_t. The compact set {(t,z):dist(z,F_t)≥η} contains no exact fit. The continuous maximum moment error therefore has a strictly positive minimum κ there. Any competitor with uniform moment error below κ is within η of a unique point of F_t. The closest point varies continuously, producing a section of the finite covering. No such section exists, by its cyclic monodromy. This proves the gap. It is an existence constant, not a numerical or optimal estimate. The argument remains valid for the smaller class of ordinary state-emitting HMMs.

## 7. What this does and does not establish

The example supplies two families with the same trivial observable bundle and the same pointwise minimum three: the constant mixture family admits a global three-state positive realization, whereas the rotating family needs four. Thus bundle topology alone does not determine temporal positive resources. The additional structure is the invariant predictive simplex and its covering of extremal states.

The hold process is deliberately nonmixing. A strictly positive finite-state transition would mix and make distant-output correlations decay, whereas the exact hold law retains nonzero component correlations at arbitrary lag. Thus no such strictly positive transition realizes the hold law. Small refresh perturbations may remove the rigid diagonal argument; robust or primitive variants require another theorem and are not asserted.

The parameter topology and continuity obligation are still supplied. An arbitrary finite set of parameter samples cannot establish this global obstruction without regularity/coverage assumptions. The result does not claim that latent component names are observable; rather, it proves a cost when a native interface requires globally continuous fixed labels.

All comparisons above keep t fixed within a word. Products at changing t would contain Q(t)L(t′), generally not the identity, and need a separately specified transport rule.

A broader next theorem could characterize continuous positive widths by equivariant maps from the identifiable-component cover into spaces of disjoint-support probability rows. The four-slot path is a concrete such map, not yet a general classification. That direction must be compared with deleted-simplex configuration spaces, equivariant obstruction theory, and positive-realization literature before claiming new structure.

## 8. An exact circle classification for distinct held components

The triangle is a special case of a complete statement for held finite mixtures. Let a continuous family over S¹ specify an **unordered** set of p distinct probability vectors v_1,…,v_p over a fixed finite output alphabet, with uniform mixture weights. The atoms need not be affinely independent. Lift the labels continuously to t∈[0,1]; their endpoint permutation is σ∈S_p, defined up to conjugacy. Denote its permutation matrix by P_σ. Every word law is the uniform mixture of the corresponding IID component laws.

For p≥2, with fixed parameter within each word:

    pointwise stochastic and real width = p;
    global continuous stochastic width = p if σ=id, and p+1 otherwise;
    global continuous normalized signed width = p if sign(σ)=+1,
                                               and p+1 if sign(σ)=−1.

The same signed-width statement holds for unconstrained real realizations: an odd permutation obstructs triviality of the full rank-p response bundle, not merely its centered part. For p=1 every width is one.

**Rank and finite-horizon proof.** At a fixed parameter, for each atom i and each j≠i choose an affine linear polynomial ℓ_ij on the output-probability space that vanishes at v_j but not v_i. Their product, normalized at v_i, has degree p−1 and takes value one at v_i and zero at every other atom. Monomials of degree at most p−1 are probabilities of words of those lengths, including the empty word. Thus evaluations of this fixed finite collection of words span R^p. The prefix/suffix Hankel block using all words of length at most p−1 has rank p. Its inserted-symbol blocks use word lengths at most 2p−1.

Any p-state realization matching these blocks is minimal and similar to the diagonal held-component model, by rank-factorization of the Hankel block. Summing inserted-symbol blocks forces the total transition to I_p. In a positive model every outcome kernel is diagonal, and its distinct joint diagonal tuples enumerate the component atoms. Hence a continuous p-state positive realization exists exactly when the cover has trivial monodromy.

**Positive upper bound with one spare slot.** Begin with Q_0=[I_p 0] and L_0 consisting of the p coordinate decoder rows followed by the uniform row. Any permutation σ can be implemented using p+1 slots: move one occupied component into the vacant buffer, move components one by one into the newly vacant slot according to the desired permutation cycle, then fill the final slot from the buffer. Repeat for disjoint cycles. Recolor a decoder row only while its slot is empty, and move Q mass only between slots carrying the same decoder unit vector. This gives QL=I_p throughout and endpoints Q_1=P_σQ_0, L_1=L_0P_σ^−1. The native lift (5) is therefore continuous, positive, normalized, and periodic. Smooth data permit a smooth lift through flat stage interpolants.

**Signed upper and lower bounds.** If σ is even, P_σ restricts to an element of SO(p−1) on 1⊥. Choose a path S(t) in that group, extended to fix 1, from I to P_σ. Conjugation by S(t) gives a global signed p-state realization with fixed initial uniform row and terminal 1. If σ is odd, the observable rank-p bundle is the bundle associated with the component permutation cover: coefficients of the component continuation laws give its local frames, and the polynomial separation argument proves their independence. Its monodromy has negative determinant, so it is nonorientable. A minimal global p-state real realization would trivialize it, which is impossible. The positive p+1 construction supplies the matching signed/real upper bound.

The compactness proof in Section6 applies with p! separated exact fibers and horizon 2p−1, giving a uniform finite-moment exclusion gap for any nontrivial σ. These results are elementary combinations of finite-mixture identifiability, minimal realization, permutation covers, and one-spare-slot lifting; none of those mechanisms is claimed new.

For every odd p≥3, p distinct emission points on a small regular p-gon in a two-dimensional zero-sum plane, rotated by 2π/p around the parameter loop, give a nonidentity even p-cycle. They therefore have signed width p and positive width p+1. The gap stays one; it is not an unbounded additive separation. The emission alphabet can remain three because polynomial continuation features, rather than affine independence of individual emissions, provide rank p.

## 9. Numerical regression

`monodromy_native_checks.py` checks 287 parameter locations, including all stage endpoints. It verifies QL=I, the endpoint permutation gluing, the constant invertible Hankel block, the normalized signed model, statewise comparisons for hold/cycle/refresh, the exact transition-then-emission HMM factorization, and seven-step adaptive-compatible word products. The largest residual was below 8×10^−16; the minimum tested emission probability exceeded 0.17. The signed kernels did have negative entries, as required by the theorem. These computations test formulas, not the covering-space impossibility or novelty.

## 10. Prior-art controls and source status

- Minimal realization through Hankel rank and similarity is classical; here a finite invertible block supplies the complete proof. Anderson's 1999 positive realization paper and Vidyasagar's survey treat all-word laws and invariant polyhedral cones. Their cone-generator lift is the direct antecedent of (5). [Anderson DOI](https://doi.org/10.1007/PL00009846), [Vidyasagar primary manuscript](https://personal.utdallas.edu/~mxv091000/Research/hmm-full.pdf#page=1).
- Mixture components being identifiable only up to permutation, and the resulting label-switching problem, are long-established. Stephens's paper directly studies that issue; it does not establish the exact four-state continuous-repair theorem claimed here. [Stephens, 2000, author PDF](https://stephenslab.uchicago.edu/assets/papers/Stephens2000b.pdf).
- Mond–Smith–van Straten's factorization-space topology and Hazewinkel's families of realization bundles are strong conceptual predecessors. The present example distinguishes a finite-component cover from its associated vector bundle, a standard distinction in topology. It must not be promoted merely by renaming label monodromy.

- **Monràs–Winter, “Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem.”** Definition5 explicitly uses a stochastic sum of nonnegative outcome matrices and fixed terminal (1,…,1). Theorem6 gives the invariant pointed-polyhedral-cone criterion; Section4 treats minimal quotient realizations and their similarity. These directly precede the native semantics and ordinary realization mechanisms used here. The inspected text does not provide a parameter-family minimum-width formula. [Primary text](https://arxiv.org/html/1412.3634).
- **Allman–Matias–Rhodes, “Identifiability of parameters in latent structure models with many observed variables.”** Theorem8 and Corollary11 identify mixtures from three observed variables under linear-independence or marginal-rank hypotheses, up to permutation. This is stronger general mixture-identifiability prior art than the elementary special proof here. The reduction from an arbitrary three-state HMM to a diagonal mixture uses the additional identity-transition structure. [Primary PDF](https://jarhodesuaf.github.io/papers/Latent.pdf).
- **Byrnes, “On certain problems of arithmetic arising in the realization of linear systems with symmetries,” 1980.** Section1 explicitly studies continuous families of Hankel data, the failure of minimal continuous matrix realization, the circle/Möbius example, and bundle-valued realizations. Thus parameter topology in realization is emphatically classical. The distinction here is that the response vector bundle is trivial while the identifiable extreme-state cover is not. [Primary text](https://www.numdam.org/article/AST_1980__75-76__57_0.pdf).

- **Vandermeulen–Scott, “An Operator Theoretic Approach to Nonparametric Mixture Models.”** The inspected primary paper gives (2p−1)-identifiability for arbitrary p-component grouped-sample mixtures, and three-sample identifiability for linearly independent components. Thus the finite-horizon mixture threshold in Section8 has a direct prior-art analogue and is not claimed new. The circle-monodromy and continuous spare-state repair are additional family questions. [Primary PDF](https://web.eecs.umich.edu/~cscott/pubs/aos_mixture.pdf).

This is not an exhaustive source audit. The conservative deliverable is the explicit theorem, its finite-moment proof and native four-state repair, not a claim of priority.
