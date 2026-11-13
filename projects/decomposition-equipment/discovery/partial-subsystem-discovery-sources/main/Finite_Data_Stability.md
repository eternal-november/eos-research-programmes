# Finite-data stability of partial subsystem discovery

This appendix supplies a conditional statistical theorem, not an implemented estimator. It reuses the compact three-view calibration argument of `local_mechanism_discovery_20261028/main/Dynamic_Product_Atlas_Discovery.md`, reproduced in outline below. No full-exterior Markov or mixing assertion is inferred from local closure.

## Calibration and bounded-table reconstruction
Fix maximum latent rank r, sensor alphabet bound, mixture weight floor pi0>0 and minimum singular value sigma>0 for each sensor matrix. On the compact class C of stochastic three-view channels and positive mixture weights obeying these floors, the tensor map Phi is injective modulo simultaneous latent labels. Its inverse is locally analytic: select an invertible rank-r two-view minor, contract the third view to obtain distinct eigenvalues, recover spectral projectors, normalize, then recover the remaining channels by left inverses. Full column rank guarantees some such contraction; finitely many minor/column choices and a finite moment-curve family suffice. Compactness supplies a finite cover by these inverse charts. Bounded inverse derivatives locally and positive separation away from these neighborhoods give a finite C_cal with

  min_labels ||theta-theta'||_1 <= C_cal ||Phi(theta)-Phi(theta')||_1.

This constant is defined, not numerically evaluated. A minimum-distance fit in C to a raw tensor with one-norm error d0 has parameter error at most 2 C_cal d0. Approximate optimization requires adding its tolerance. Unknown rank is recovered by the two-view singular-value floor pi0*sigma^2, when d0 is below half this floor.

Let R be a common maximum latent rank. True and fitted sensor left inverses have norm at most B=max(1,sqrt(R)/sigma). The Gram inverse identity yields a conservative inverse error

  eta = 2 sqrt(R) (sigma^(-2)+2R sigma^(-4)) C_cal d0.

For a bounded aligned table using at most ell noisy sensor variables, tensor-product inversion and telescoping give latent error before normalization at most

  zeta0 = (B+eta)^ell d0 + ell*eta*(B+eta)^(ell-1).

Nearest one-norm projection onto the probability simplex gives error zeta=2*zeta0. This applies to history tables because conditional sensor noise is independent over the aligned path. It does not assume the latent path is Markov. Labels must be aligned consistently across calibration and history tables; a fixed fitted channel does this for a given patch.

Let every conditioning cell used by the algorithm, including the randomized regime, have probability at least rho. If zeta<rho/2, conditional rows have one-norm error at most nu=4*zeta/rho. For context recovery under changed input policies retain the main theorem's coverage of every candidate pair-union, not just the selected context.

## Separated finite discovery theorem
Assume the population theorem's causal and support promises. Add the following positive separation margins, uniformly over the finitely many partitions and contexts of the bounded patch universe:

1. Every hidden-mode-dependent partition has some block, old state and true response context with absolute mode contrast at least gamma.
2. Every insufficient candidate context, for a partition that passes the probe test, exceeds its optimal conditional entropy by at least Delta_H. If all candidates are sufficient, no gap is needed.
3. Every nonzero kernel response distinction used for state refinement, boundary response partitioning, or input-subset removal has size at least lambda. This is an entry/block-sum margin; positivity alone does not imply it.
4. A learned task-emission signature has a gap between distinct signatures, and is estimated accurately enough to recover its equality partition. Alternatively the task partition is supplied exactly.

All bounds concern finite local objects, not the unknown exterior state count. They may become arbitrarily poor near nonidentifiability.

Uniform conditional-row error nu bounds the error of every partition block probability by nu, simultaneously for ALL partitions: summation is a contraction in one-norm. Consequently no union bound over adaptively chosen partitions is needed beyond the bounded raw-table event.

The observed probe difference is zero for a valid block response, and at least delta*gamma for a witness of invalidity. Each estimated difference has error at most 2nu. If 4nu<delta*gamma, threshold delta*gamma/2 gives exactly the population probe decisions.

For entropy let F_M(t)=t log(M-1)+h_2(t) for M>=2 in the small-error range, F_1=0. With bounded joint/context alphabets J1,J0, a uniform conditional-entropy error bound is

  E_H = F_J1(zeta/2)+F_J0(zeta/2).

Choose a near-minimum tolerance tau with 2E_H<=tau<Delta_H-2E_H, requiring Delta_H>4E_H. This retains every genuinely sufficient context and excludes every insufficient context. Select a smallest retained context if desired. Exact empirical argmin with cardinality tie-breaking is not the estimator.

The selected context therefore is genuinely sufficient. Its estimated conditional rows are probability vectors. If an extra row projection is used, let e=2nu be a conservative final row-error bound; without it e=nu suffices. Comparing two response signatures has entry error at most 2e. If 4e<lambda, threshold lambda/2 recovers every state split, input dependency and initial boundary-response distinction exactly. Deterministic successor refinement of the boundary register is then exact combinatorics. The recovered final quotient and boundary partitions match their population versions, up to latent labels. This also recovers a correct finite obstruction when the population algorithm fails; the causal interpretation remains conditional on the declared experiment/model promises.

## Sampling statement
Let Q be the number of bounded raw tables requested, including all candidate contexts, pair-union coverage tables, regime tables and calibration tables. Let J bound their raw alphabet sizes. For independent windows from the declared exploration distribution, coordinate Hoeffding and a union bound show that

  N >= (J^2/(2*d0^2))*log(2QJ/alpha)

samples per requested table suffice for simultaneous one-norm error at most d0 with probability at least 1-alpha. Overlapping windows from a single trajectory are NOT independent; they require an explicit mixing/concentration replacement, which arbitrary hidden exteriors do not automatically provide. Data acquisition may use independent runs or another justified sampling design; no state-reset oracle revealing component membership is assumed.

Choose d0 small enough for the rank, coverage, probe, entropy, task-signature and response-margin inequalities above. Such a positive value exists under the stated strict margins. This yields a finite-sample theorem, with Q polynomial in the channel-bank size at fixed d,k,L and alphabet bounds. Neither C_cal nor this sample budget is claimed numerically practical; fixed-dimensional minimum-distance calibration is a mathematical estimator, not a furnished scalable optimizer. Bit precision and optimization tolerances must be charged in implementation.

## What the estimated local kernel guarantees
On the correct-structure event, suppose final local row error is e in one-norm. Under the SAME causal input policy on the retained comparison transcript (or same imposed input sequence), common initial local/interface law, and the same observation channel factoring through the recovered quotient and boundary, a sequential coupling gives H-step retained local transcript total variation at most min(1,H*e/2). Add initial-law and observation-channel errors separately. Raw full-patch sensors need not factor through the quotient; this bound does not cover their transcripts from the quotient kernel alone. A whole lifted comparison would additionally have to retain identical conditional remainder kernels and initial residual law. If a policy uses omitted private information, a common coupled extension or its conditional input kernel must also be supplied; naming the same physical controller alone is not sufficient. Different exterior policies can generate different input histories and therefore different unconditional local laws, even though the open response kernel is invariant. Hidden physical hazards and unrestricted infinite-horizon safety do not follow from this statement.
