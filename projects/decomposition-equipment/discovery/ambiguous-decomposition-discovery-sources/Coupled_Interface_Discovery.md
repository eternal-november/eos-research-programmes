# Discovering an initially invisible persistent interface graph

28 October 2026. Restricted extension of `Partial_Process_Gluing.md`. This uses the standard covariance-regression identity for generalized binary vector autoregressive/noisy-copy models; that identity is not claimed as new. The contribution here is its explicit connection to inferred source residuals, pair-history invisibility, positive process realization and bounded-width richer probes.

## 1. Model and theorem

Retain the discovered site process, three rings, m source triples and calibrated readout channels of `Ambiguous_Family.md`. Write n=3m and r_X=1-q1-q2>0. Replace the independent binary source chains by an autonomous spin process H(t) in {-1,+1}^m:

* At source b, independently at every tick, select parent c with probability a_bc, or select fresh with probability r_b=1-sum_c a_bc.
* On a parent selection set H_b(t+1)=H_c(t); on fresh selection draw an independent fair spin.
* Selectors and fair draws are independent across source-time and independent of the site-process selectors, the independent randomness used to sample source emissions conditional on H, and sensor noise. The actual E outputs need not be independent of H.

A_H=(a_bc) is unknown, nonnegative, and has bounded row support d. Assume r_b>=r_H>0. For the reconstruction theorem additionally assume A_H is nonsingular, with a positive lower singular-value margin for quantitative recovery. One admissible growing example is an unknown ring with A_H=aP+bP^2, a>b>0, a+b<1; sigma_min(A_H)>=a-b. Independent persistent binary chains are the diagonal example a_bb=lambda_b>0.

Conditional on the complete H path, source tuples E_b(t) are independent over (b,t), with

    P(E_b(t)=e | H_b(t)) = q_0(e) + [t0_b + delta_b H_b(t)] (-1)^|e|,
    delta_b>0,  t0_b +/- delta_b in [-1/190,1/190].

The independent event draws conditional on H are part of the model. H is exogenous to X: no X or E feedback enters H's update. Positive delta fixes the source-state sign gauge. A positive gain lower margin is needed for stable finite-sample reconstruction, not for the exact population identities.

**Theorem.** All admitted fixed-pair X history laws are independent of A_H,t0,delta. Nevertheless, means and lag-one/lag-two covariances of the richer triple residual statistics defined below reconstruct t0,delta,A_H exactly in this class. Each required moment is accessible from at most 18 named noisy site ports over at most four consecutive ticks. Every parameter candidate satisfying the displayed positivity and noisy-copy constraints has an explicit positive stationary process implementation with n+m online persistent bits and local tables, and an exact two-level ancestor initializer. No global hidden-state table is used.

This is a richer-evidence discovery theorem, not identification from the original pair evidence. Singular A_H, zero gains, arbitrary H dynamics and hidden feedback from X are outside this reconstruction claim.

## 2. Why the original evidence remains completely blind

For any fixed one or two causal rings, each source contributes at most two innovation coordinates. Their conditional marginal is independent of the value of H_b(t). Conditional independence across source-times therefore implies that the entire projected innovation trajectory has a fixed product law even conditional on the complete coupled H path. The same causally closed ring-projection argument as before proves exact pair-history invariance. Coupling source states across b does not change that proof.

Thus genuinely different hidden persistent interface graphs, including independent chains and coupled cycles, survive the complete original observation contract. Their full process laws may differ; the richer reconstruction below provides a separating experiment within the stated nondegenerate class.

## 3. Observable residuals and the lag identity

For discovered source b=(i,j,k), define the bit-valued site's residuals and triple product as in the earlier note:

    U_i(t)=X_i(t+1)-p-sum_l A_il(X_l(t)-p),
    W_b(t)=U_i(t)U_j(t)U_k(t).

The triple-table parity perturbation changes the centered cubic moment by minus its coefficient. Thus, conditioning on the complete H path and the complete pre-update X history,

    E[W_b(t) | H_path, X_past] = r_X^3 (kappa0-t0_b-delta_b H_b(t)).

The unique stationary source law has E H_b=0: its mean obeys mu=A_H mu, and ||A_H||_infinity<1. Since each H_b is a spin, C_H,bb=Var H_b=1. Hence

    M_b=E W_b=r_X^3(kappa0-t0_b),
    V_b(t)=-(W_b(t)-M_b),
    E[V_b(t)|H_path,X_past]=g_b H_b(t),  g_b=r_X^3 delta_b>0.

The minus sign is essential for bit coordinates; using W directly gives negative gains but the same covariance matrices.

For s>t, V(t) is part of the pre-update history available when conditioning V(s). Conditional on the complete H path, the tower property first replaces V(s) by G H(s), and then V(t) by G H(t), where G=diag(g_b). Therefore

    E[V(s)V(t)^T | H_path]=G H(s)H(t)^T G.

This does not assert that residual noise is independent through time or that same-time residual covariances are noise-free. H's linear conditional mean gives E[H(t+k)|H(t)]=A_H^k H(t). Consequently, with future-first orientation,

    Gamma_k := Cov(V(t+k),V(t)) = G A_H^k C_H G,    k>=1.

The strict restriction to positive lags avoids the same-time residual-noise term.

Conditional on H(t-1) and all H selectors, every refreshed coordinate has an independent fair spin. Total covariance then gives C_H >= diag(r_b) >= r_H I. Together with nonsingular A_H and positive G this proves that Gamma_1 and all matrices inverted below are nonsingular.

## 4. Reconstruction and certificates

Compute solely from richer residual moments

    B = Gamma_2 Gamma_1^{-1} = G A_H G^{-1},
    S = B^{-1} Gamma_1 = G C_H G.

Since C_H,bb=1,

    g_b=sqrt(S_bb),
    delta_b=g_b/r_X^3,
    t0_b=kappa0-M_b/r_X^3,
    A_H=G^{-1} B G.

The support of A_H is the previously invisible persistent source-interface graph. In particular, a nonzero off-diagonal entry discovers a source-to-source persistent input wire, not merely colored noise at an isolated source.

Necessary membership checks include symmetry/positive definiteness and unit diagonal of G^{-1}SG^{-1}; entrywise nonnegativity and allowed row support of A_H; positive refresh margin; and positivity of t0_b +/- delta_b. Also check the stationary covariance equations, writing C=G^{-1}SG^{-1}:

    C_ii=1,    C_ij=(A_H C A_H^T)_ij for i!=j.

These equations are necessary because different source updates are conditionally independent given the old H state. They are sufficient for covariance consistency: on matrices with diagonal fixed at one, the off-diagonal update is a max-entry contraction with factor at most (1-r_H)^2<1. Its unique fixed point is the covariance of the unique stationary positive noisy-copy process. This direct matrix check costs O(m^3). Without it, positive definiteness and admissible A_H alone would not certify the measured covariance.

Failed checks reject this declared model class. Passing these algebraic checks and constructing the displayed process verifies the used summary equations; it is not a substitute for comparing any additional trajectory evidence the user may supply. In exact model-generated data the theorem recovers the actual parameters.

Dense linear algebra costs O(m^3), with O(m^2) summary storage. Stability depends on explicit positive margins for r_X,r_H,g_min,sigma_min(A_H), sensor attenuation and nonzero edges. With these margins, ordinary inverse-matrix perturbation and bounded-observation concentration give polynomial sample requirements; no optimized exponent is asserted. A zero-versus-positive edge decision without an edge margin is not certified by finite samples.

## 5. Probe width, timing and access

A single W_b(t) is a polynomial of three next-time site bits and at most six current parent bits. The product W_b(t+k)W_c(t), k=1 or 2, uses at most 18 named ports. At k=2 its time locations lie in t,t+1,t+2,t+3; k=1 needs only three ticks. Arbitrary duplicates reduce the distinct-port count.

The BSC noise at each port/time is independently calibrated. Expand the required polynomial, reduce repeated powers of the same binary latent variable using X^a=X for a>=1, and invert the one-variable emission moment channel in each distinct port/time coordinate. This gives the required latent polynomial expectation from the noisy joint law. One must not multiply separately denoised repeated copies as though their sensor noises were independent. Degree is at most six before binary reduction, so there is no dimension-growing deconvolution order.

This is an explicitly stronger same-run mask contract than the original two-port observations. It requires O(m^2) source-pair/window choices, each of bounded width and length, plus source means. It does not silently treat independent original pair runs as joint richer samples. Long-run concentration must account for mixing of both H and X; the old n*q_X^t bound alone does not control arbitrary H initialization.

## 6. Exact stationary realization without a global table

First trace the n requested X(0) bits backward through the independent site selectors until each takes its fresh-source branch. Merge repeated site-time visits. This needs expected at most n/r_X visits and produces at most n terminal source-time queries H_b(t), with t<0.

Include all m queries H_b(0), needed for online continuation. Resolve these at most n+m H queries by a second backward graphical tracing procedure: at each H site-time, follow the single selected H parent, or stop at its fair innovation. Cache and reuse every named H selector and fair innovation occurrence across all query traces. Each H lineage has conditional expected length at most 1/r_H. The X query set is independent of the H selectors, so the expected total ancestry work is bounded by

    n/r_X + (n+m)/r_H,

before cache savings. Sample each requested E_b(t) tuple once conditional on the resulting H_b(t), and reuse its coordinates across terminal X requests. This yields jointly correct (X(0),H(0)). Sampling a fresh independent H value at each X terminal would be incorrect.

Both ancestor systems terminate almost surely. Their bilateral construction is shift invariant, satisfies the update equations, and couples away earlier states. Thus it gives the unique joint stationary law. The source graph may have cycles; selected-parent ancestry still follows one path, not all graph parents.

For hard resource caps T_X,T_H on the respective lineage lengths, a union bound gives failure probability at most

    n*(1-r_X)^T_X + (n+m)*(1-r_H)^T_H.

Arbitrary fallback after failure yields at most this total-variation error. Exact initialization is Las Vegas with unbounded worst-case scratch space. Online storage is n+m persistent bits (plus overwrite-safe buffers), O(n+md) local table entries and O(n+md) potential local input wires. Sensor noise, selectors, source innovations and their transport are charged as before.

## 7. Crossing coherence and evidence restriction

Extend the common named fine record graph of `Partial_Process_Gluing.md` by the H parent-read wires, H selectors and fair innovation occurrences. Each H_b register is still owned once by source b. Ring grouping retains source components and their H network as shared boundary providers; source-column grouping places H_b with its associated three X sites, with H parent messages crossing source columns. Regrouping remains an explicit probability-preserving bijection of complete records for every fixed parameter world. It does not erase H, independently resample source records, or invoke planar interchange.

Let Theta be the positive parameter domain compatible with original pair evidence. A richer evidence set E' defines Theta'={omega in Theta: L_omega satisfies E'}. Restricting the family of complete records to Theta' commutes literally with ring/column regrouping, since each regrouping preserves the same omega and the same complete record. For the richer summaries of Sections 3-4, a nondegenerate actual member is reconstructed rather than averaged across Theta.

The world tag omega is an index of a fixed mathematical model/program configuration, not a dynamic hidden state register. A finite program stores its selected numeric parameter tables as charged description data; no execution switches omega after seeing outcomes. The theorem says: for each omega, one shared process has coherent ring and column presentations; richer evidence narrows the set of omega. It does not claim a single fixed whole law realizes all different omega, or that pair evidence alone chooses the true source graph.

## 8. Limited numerical check

`check_coupled_interface.py` and `Coupled_Interface_QA.json` independently verify covariance/gain reconstruction for an isolated three-spin H ring (eight states), with synthetic positive gains. Maximum A recovery error is below 1.3e-16 and gain error below 4.4e-19. This checks the covariance algebra on a small fixture; it is not a simulation of the full residual X/H process or a replacement for the conditional-path proof. The finite enumeration is confined to this QA fixture, not the growing-family discovery method.
