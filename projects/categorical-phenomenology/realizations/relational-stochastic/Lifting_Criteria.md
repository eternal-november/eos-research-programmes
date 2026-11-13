# Independent native-lifting criteria and coherent resource transport

These are finite matrix statements, not novelty claims. They supplement the shared zerosumfree-semifield two-stage realization theorem. Finite nonempty J,S,I are used throughout; w_s>0, sum_s w_s=1, Q is row-stochastic, and R is nonnegative with total mass 1 and no zero row. Put

P(Q,R,w)={T>=0 : TQ=R, 1^t T=w^t}.

The native-cost theorem in the main report identifies stochastic anchored native cost with 2+min_{T in P} rank_+(T), and its Boolean version with 2+min Boolean factor rank. Thus the following criteria concern actual native witnesses and resources, not only generated observable images.

## 1. Input-only convex compatibility criterion

Regard R as a vector in R^{J x I}. For each s define
V_s={ e_j tensor Q_s : j in J },
and define the Minkowski polytope
C(Q,w)=sum_s w_s conv(V_s).
Then P(Q,R,w) is nonempty iff R belongs to C(Q,w).

Proof: a column T_{-,s} has total w_s, so coefficients T_js/w_s form a probability vector on J. Its contribution to TQ is w_s sum_j (T_js/w_s)(e_j tensor Q_s). Conversely decompose a point of the stated Minkowski sum and multiply its simplex coefficients by w_s. This is not a hidden native-feasibility hypothesis: C(Q,w) is constructed directly from supplied Q,w, independently of unknown T or a realization.

Equivalently, for every tuple of real test vectors u_j in R^I,
  sum_j <u_j,R_j> >= sum_s w_s min_j <u_j,Q_s>.     (1)
Finite-dimensional separation proves sufficiency; minimizing a linear functional over a Minkowski sum proves necessity. Facet enumeration gives a finite test in principle, while the original LP is usually more practical. Do not claim that the universal test-vector form is itself an efficient procedure.

This is a standard convex/transportation description of the finite Blackwell garbling feasibility problem after Bayesian reversal, not a new general criterion for arbitrary latent dynamics.

## 2. Exact support lifting is relative-interior membership

Let E subset J x S have every column nonempty. Define
C_E(Q,w)=sum_s w_s conv{e_j tensor Q_s : (j,s) in E}.
Then:
(a) There is a feasible T with support(T) subset E iff R in C_E(Q,w).
(b) There is a feasible T with support(T) exactly E iff R in relint C_E(Q,w).

Proof (b): let D_E be the product over s of simplices on E_s={j:(j,s) in E}. Its relative interior consists exactly of strictly positive coefficients in every allowed coordinate. The linear map L:D_E -> R^{J x I} sends coefficients to sum_s w_s sum_j coefficients_js(e_j tensor Q_s). The standard finite-dimensional identity L(relint D_E)=relint L(D_E) applies, including duplicate vertices and lower-dimensional images.

Elementary proof avoiding a convex-analysis citation: the image of any all-positive coefficient tuple cannot lie in a proper supporting face, because equality in the supporting inequality forces equality at every allowed vertex, hence on the entire image. Conversely, take y in relint(image) and z=L(x0) for a fixed all-positive x0. If y=z use x0. Otherwise extend the segment from z through y slightly past y to y' in the image (relative interior permits this). Write y=epsilon z+(1-epsilon)y', choose any preimage x' of y', and use epsilon x0+(1-epsilon)x', which is all-positive.

An entirely input-only dual version replaces min_j in (1) by min_{j in E_s}. Require all resulting inequalities, and require that equality can hold only when, for every s, the values <u_j,Q_s> are the same for all j in E_s. Indeed this says R belongs to the polytope but lies in no proper supporting face. It automatically handles affine-hull constraints: functionals constant on the polytope are allowed to achieve equality.

For rational Q,R,w, the support-constrained feasibility problem has rational witnesses whenever it has real witnesses. This does NOT imply rational minimum latent factorizations: the subsequent nonnegative-rank optimization is a different problem and can require irrational factors.

## 3. Exact Boolean existence criterion

Use Boolean matrix multiplication (OR of AND). Assume every row Q_s and R_j is nonempty, and w_s=true for every s. Write B_s=support Q_s and C_j=support R_j. Put
  S_j={s : B_s subset C_j}.
A Boolean T satisfying TQ=R and every column of T nonempty exists iff
  union_{s in S_j} B_s = C_j for every j,
  union_j S_j = S.

Proof: any feasible T can only use pairs (j,s) with B_s subset C_j, so T is bounded above by the maximal relation E_max={(j,s):s in S_j}. The latter cannot create an unwanted output. Existence requires that it cover all required outputs in each row and all required coarse states in its columns. If these conditions hold, E_max itself is a witness. This is a non-tautological, finite inclusion/union algorithm from Q,R, not search over all T.

For an exact prescribed Boolean support E, the criterion is simply EQ=R together with every column of E nonempty. In contrast, numeric support lifting is the relative-interior criterion above.

## 4. Support maps witnesses but does not reflect feasibility

The semiring homomorphism supp:R_{>=0}->Bool commutes with finite matrix products. Therefore feasible numeric T gives feasible Boolean supp(T), and any nonnegative factorization T=A B gives supp(T)=supp(A)supp(B). Hence Boolean native anchored cost <= stochastic native anchored cost, interpreted in N union infinity. Infeasible Boolean data rule out a positive numeric lift, but feasible Boolean data need not lift.

Use the preceding report's full-support control:
 Q=[[4/5,1/5],[1/5,4/5]], w=(1/2,1/2),
 R=[[9/20,1/20],[1/20,9/20]].
The unique T=RQ^{-1} is [[7/12,-1/12],[-1/12,7/12]], so numeric feasibility fails. All Q,R entries are positive; their Boolean versions are full relations and have a Boolean rank-one T witness. Thus Boolean native cost is 3 while numeric native cost is infinite. With the same Q,w and same Boolean input, R all 1/4 gives numeric cost 3, while R diagonal37/100/off13/100 gives numeric cost4. Quantitative weighting changes cost and feasibility without changing any support data.

## 5. Coherent comparisons transport native witnesses and costs

All statements here work over the main report's commutative zerosumfree semifield K (and, for the bare equations, over a commutative semiring).

Let U:J->J', F:S->S', G:I->I' be row-normalized matrices. Suppose supplied target data satisfy
 w'=wF,  QG=FQ',  R'=U^t R G.
Then
  Phi(T)=U^t T F
maps P(Q,R,w) into P(Q',R',w'). Indeed
 Phi(T)Q'=U^t T QG=R',
 1^t Phi(T)=1^t U^t T F=(U1)^t T F=wF=w'.

If T=A B, with B row-normalized, its factorization transports to
  A'=U^t A, B'=BF,
with B' row-normalized and the same latent carrier. Consequently minimum factor rank and stochastic/normalized-link native state cost cannot increase. Zero target marginal rows/columns can be removed when the two-stage nonzero-marginal assumptions are needed.

Successive comparisons compose as (U U', F F', G G'); direct and successive witness/factor transport agree exactly by associativity. Coefficient homomorphisms, including support, commute entrywise with this law. Thus this is a coherent native resource comparison, not only a map of observable generated images.

Caution: a stochastic F need not preserve a deterministic state link. The theorem guarantees the normalized-link resource comparison. Deterministic-link preservation requires F deterministic (and care if U/G identify the phase tags; the theorem keeps stage tags separate).

The displayed comparison square is a supplied, checkable data-level hypothesis. Its existence is not asserted for arbitrary changes of interface. It is materially weaker than assuming a lift of every native realization: the lift is the explicit derived formula.

## 6. An exact observation-recovery criterion

For output-only G, take U,F identities. The feasible set always enlarges:
 P(Q,R,w) subset P(QG,RG,w).
If there exists row-stochastic H:I'->I satisfying
 QGH=Q and RGH=R,
then the two feasible sets are equal, not merely equinumerous, because TQG=RG implies TQGH=RGH and hence TQ=R. Thus all witness-dependent rank optimizations, exact support admissibility, and both native resource costs are unchanged. This criterion allows observation changes without assuming a canonical optimizer.

The same proof works over Bool or the shared coefficient semifield. It gives a sufficient recovery criterion, not a claimed necessary characterization of equality of feasible sets. More generally two valid comparison arrows give equality of optimal normalized-link costs, without implying a canonical bijection of optimal realizations.

## 7. The actual common category of native realizations

For input datum D=(w,Q,R), define W_K(D) as follows.
- Object: positive integer h, A in K^{J x h}, row-normalized B in K^{h x S}, such that AB is in P_K(D).
- Arrow (h,A,B)->(h',A',B'): row-normalized C in K^{h x h'} with AC=A' and CB'=B.
Identities and composition are matrix identities/products. For composable C,D, A(CD)=A'' and (CD)B''=B. These are genuine stochastic/Boolean middle-state simulations, not just equality of external behavior.

Each arrow preserves the full coupling T=AB, since A'B'=ACB'=AB. Thus different feasible couplings are deliberately not collapsed by the category. There is a functor W_K(D)->P_K(D)_discrete, retaining this joint witness. The h-state realization also includes the two tagged phase states, so the cost of an object is h+2. This cost is a statistic on objects, NOT claimed monotone along all arrows (simulation matrices can change h either direction).

Every abstract factorization T=A0 B0 of inner dimension h over a nontrivial zerosumfree semifield admits the required normalization: delete zero rows of B0; for each remaining row set d_v=sum_s B0_vs, which is nonzero by zerosumfreeness. Put B_vs=d_v^{-1}B0_vs, A_jv=A0_jv d_v. Thus min object cost equals 2+min feasible semiring factor rank. If an intermediate row has A0 column zero it may also be deleted. No abstract completion or additional non-free state object is used.

The input comparison (U,F,G) from Section 5 defines the functor
 W_K(D)->W_K(D'), (h,A,B)->(h,U^t A,BF), C->C.
The arrow equations follow from U^t AC=U^t A' and C(B'F)=BF. These functors compose strictly and preserve the presented h. Therefore optimized cost is nonincreasing even though objectwise cost is not a functor on the native-simulation category.

A coefficient homomorphism phi:K->L maps the entire category entrywise, including input data and arrows, and commutes with the comparison functors. In particular support yields W_R(D)->W_Bool(supp D). It is not essentially surjective in general: some qualitative native presentations have no stochastic lift, even when qualitative data are fully supported.

CRITICAL LIMITATION. Sections 1–2 characterize existence of some native refinement and, more sharply, some refinement with prescribed coupling support E. They do NOT characterize a lift of an arbitrary prescribed Boolean factorization (h,A_bool,B_bool), nor guarantee a stochastic lift at the same h. The rank-constrained question is an additional constrained nonnegative factorization problem. The full-support numeric cost-3/cost-4 example makes this failure visible at the same qualitative input. Exact category-object lifting also requires attention to label permutations/isomorphisms rather than mere cardinality. No claim of an independent general fixed-resource criterion follows from the relative-interior theorem.

## 8. Sharp resource boundary: one middle state, and arbitrary NMF

There is a one-middle-state normalized-link realization exactly when
  R_{ji}=p_j mu_i, where p_j=sum_i R_ji and mu=wQ.
This holds over the shared coefficient semifield, not only probabilities. For h=1, normalized B is a row vector. Because T=A B and total T is 1, normalized B implies sum_j A_j=1. Column T=w therefore forces B=w, and row T=p forces A=p. Hence R=TQ=p tensor mu. Conversely A=p,B=w constructs a witness.

Over probabilities this is ordinary independence of the early label and late output. Over Bool, every p_j is true, and it says all R_j equal the union of all coarse Q_s. Thus even the optimal three-state boundary has a shared input-only interpretation with distinct native semantics.

At the other end, let Q=I_S, let R be any row-nonzero nonnegative matrix of total mass 1 with every column positive, and set w=1^t R. Then P(Q,R,w)={R}. Consequently the exact native resource problem is 2+rank_+(R). Thus arbitrary finite NMF already occurs as a special case; coefficient support forgets genuine native resource information. This is a reduction identifying the remaining classical problem, not a novelty claim or an argument that all constrained instances are easy.

Any feasible input has normalized-link cost at most min(|J|,|S|)+2, since every feasible T has factor rank at most min(|J|,|S|); deterministic-link cost remains |S|+2 under the nonzero-marginal and phase assumptions. The lower bound rank(R)+2 applies over the reals because R=TQ, and ordinary rank(T)<=nonnegative rank(T).
