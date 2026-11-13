# Independent relational/stochastic stress test

## 1. Scope and conventions

Finite sets J (first announcements), S (chosen coarse middle states), I (second outputs). Stochastic data: row-stochastic Q:S→I, strictly positive probability row w on S, and a nonnegative joint matrix R:J×I with positive row masses p and total mass one. Require 1ᵀR=wQ. The chosen coarse realization is held fixed; this is stronger than asking whether the fine observed law has any realization.

The stochastic lift polytope is

P(Q,R,w)={T≥0 : TQ=R, 1ᵀT=w}.

The previous report establishes, in its homogeneous phase-tagged two-stage model, existence iff P is nonempty, stochastic-link state cost 2+min_{T∈P}rank₊T, and deterministic-link state cost |S|+2 whenever feasible. The added two states count the root and terminal phases. These claims concern this model, not arbitrary native realizations.

The Boolean counterpart uses total relations Q_B:S→I, nonempty rows of R_B:J→I, and all-one coarse initial support. Its feasible set is

P_B={T_B : T_B⊙Q_B=R_B, 1ᵀ⊙T_B=1ᵀ}.

Thus every coarse middle state must be used. Boolean multiplication is existential relational composition. Boolean rank is minimum rectangular-cover/factorization cardinality.

## 2. A derived support comparison

Support is a semiring homomorphism from nonnegative reals to Booleans: supp(a+b)=supp(a)∨supp(b), supp(ab)=supp(a)∧supp(b). Consequently a stochastic feasible T induces a Boolean feasible supp(T) for the supported data. A k-factor nonnegative factorization T=AB induces the k-factor Boolean factorization supp(T)=supp(A)⊙supp(B). Therefore

rank_B(supp T)≤rank₊T,

and the minimum Boolean lift rank is a lower bound for the minimum stochastic lift rank. The map preserves concrete composite witnesses, not only their existence. Neither reverse existence nor equality of minimum resources holds.

Normalization must not be silently treated as a semiring-generic axiom: a stochastic row sums to one, whereas a Boolean row merely has an entry. The support map preserves stochastic normalization, but no converse normalization follows.

## 3. Independent fixed-support lifting criterion

Let E⊆J×S be a proposed allowed support. Define vectors

v_js=(e_j⊗Q_s,e_s) in R^(J×I)⊕R^S,

and b=(vec R,w). A lift supported within E exists iff

b∈cone{v_js:(j,s)∈E}.

Proof: the coefficients of this conic combination are precisely T_js. This converts the compatibility question into a concrete finitely generated cone with explicit generators obtained from the coarse data.

Farkas dual: such a lift exists iff every array U:J×I and vector a:S satisfying

<U_j,Q_s>+a_s≥0 for all (j,s)∈E

also satisfy

<U,R>+a·w≥0.

A violated inequality is an independently checkable obstruction. It depends on numerical geometry invisible to support.

For exact support E, the criterion is b∈relint cone{v_js:(j,s)∈E}, where relative interior is in the cone's linear span. This uses the finite-dimensional identity A(relint C)=relint A(C), with C the nonnegative orthant. An elementary computational equivalent avoids that theorem: maximize δ subject to TQ=R, 1ᵀT=w, T_js≥δ on E, T_js=0 off E, δ≥0. For nonempty E, exact-support lifting holds iff this LP is feasible and its optimum is positive. Total mass is one, so the objective is bounded. Empty E is impossible for the normalized data here.

This is a linear criterion for the composite coupling T. It is NOT a linear criterion for a chosen rank bound or for lifting an arbitrary specified Boolean factorization. Requiring T=AB with k columns in A is bilinear; preserving the supports of A and B does not remove that nonlinearity.

## 4. Full-support separation: no zeros explain the obstruction

Set

Q=[[4/5,1/5],[1/5,4/5]], w=[1/2,1/2].

The supported Q and each R below are all-one matrices. In every case the Boolean problem has the all-one coupling, of Boolean rank one. Since Q is invertible, each stochastic problem has the unique candidate T=RQ^{-1}, where Q^{-1}=(1/3)[[4,-1],[-1,4]].

* R₀=[[1/4,1/4],[1/4,1/4]] gives T₀=R₀, nonnegative rank one.
* R₁=[[37/100,13/100],[13/100,37/100]] gives T₁=[[9/20,1/20],[1/20,9/20]], ordinary and nonnegative rank two. All entries of Q,R₁,T₁,w are positive. Hence the relational minimum middle-state count is one, while the stochastic minimum is two.
* R₂=[[9/20,1/20],[1/20,9/20]] gives T₂=[[7/12,-1/12],[-1/12,7/12]], so no stochastic lift exists. The Boolean problem is unchanged.

For the last case an explicit separating certificate is U_1=(-1,4), U_2=(0,0), a=0. Its pairing with Q's first and second rows is respectively 0 and 3, hence every generator satisfies the nonnegativity requirement. But <U,R₂>=-1/4. Equivalently, no mixture of coarse rows can produce conditional probability 0.9 of the first second-stage output: the maximum available is 0.8.

These controls already occur in the previous numerical reduction; their new use is to refute fullness/resource reflection of support transport, not to claim new examples or a novel LP method.

## 5. Native Boolean state-cost justification

Under exactly the same two-stage phase-tagged model, replacing stochastic kernels by total relations and links by total relations gives cost 2+min rank_B(T_B). This requires those native conventions, not bare arbitrary relations.

Upper bound: factor feasible T_B=A⊙B through k points; remove unused factor points. Each remaining B row is nonempty, and each A row is nonempty because R_B has nonempty rows. Root-to-middle transitions for announcement j are A_j; middle emissions use B⊙Q_B, followed by the terminal phase. Link the k middle states by B to coarse S, with root and terminal linked identically. Column coverage of T_B gives the required coarse first-step link equation.

Lower bound: phase tags force reachable root, middle and terminal states to be disjoint, since their possible next outputs are disjoint. Totality and the link equations force middle-state links to coarse middle states. First-announcement reachability A and those links B therefore factor the induced T_B through the reachable middle states. This gives at least rank_B(T_B) middle states and two other states. No probability or convexity is used in this argument, only Boolean noncancellation, totality, and phase tags.

For deterministic links the same coverage requirement forces at least |S| middle states, and the direct construction from T_B attains |S|+2. Do not transfer these bounds to non-total relation semantics or models with uncounted external clock memory.

## 6. Observation-change laws carrying actual feasibility and cost

Let G:I→I' be stochastic and change Q,R simultaneously to QG,RG, retaining w and the coarse middle set. Every feasible T remains feasible, hence

P(Q,R,w)⊆P(QG,RG,w).

Therefore stochastic optimum cannot increase under this output garbling (using ∞ for infeasibility). This is stronger than ordinary rank₊(HG)≤rank₊H: it respects the chosen coarse realization and its strong link. The same proof works for total Boolean output relations, including the Boolean minimum cost. All-positive coarse weights remain unchanged.

If there is a common stochastic recovery L:I'→I satisfying QGL=Q and RGL=R, then the feasible polytopes are equal: multiply TQG=RG by L. Thus every lift and its rank is retained exactly, and both native optimum costs agree. A deterministic output renaming is a special case. In fact, for this finite linear argument any real L satisfying both equations suffices; stochastic L is the semantically meaningful sufficient condition. Recovery of R alone does not justify the conclusion, nor recovery of Q alone.

The converse implication is not claimed: equality of feasible polytopes can hold without a common stochastic recovery. Resource equality alone is still weaker. General output garbling may strictly lower cost or restore feasibility because it removes constraints.

## 7. What this does and does not establish

A category of factorization diagrams plus a minimum-cardinality function is largely an encoding; it does not by itself solve a new realization problem. The concrete content here is (a) witness-preserving support transport with a quantitative lower bound, (b) exact finite numerical lift obstructions over a Boolean witness, and (c) observation-change inclusion/equality laws for the native feasible sets and resource optima.

This does not yet unify predictive filtering, positive dynamical realization, and arbitrary stochastic latent minimization. Nor does it infer primitives from an arbitrary experience stream. It does demonstrate a common realization problem with transport laws that retain more than the generated observable image, in a bounded relational/stochastic family. Standard ingredients should be credited as standard: semiring support, Boolean/nonnegative rank, Farkas separation, and finite factorization constructions.

## 8. Stronger controls: unbounded resource gap and strict garbling

The support-induced resource underestimate is not bounded by a constant. For n≥2 let U_n be the n×n all-1/n stochastic matrix, choose ε,δ in (0,1), and put

Q=(1−ε)I+εU_n,
T=((1−δ)I+δU_n)/n,
w=(1/n,…,1/n), R=TQ.

All entries of Q,T,R are strictly positive. Q is invertible (eigenvalues 1 and 1−ε). Consequently T is the unique lift; T has rank n (eigenvalues 1/n and (1−δ)/n), so rank₊T=n. The Boolean data are all-one and admit rank-one T_B. Thus stochastic native cost is n+2 whereas Boolean cost is 3. This proves an arbitrarily large additive and multiplicative gap within this model, with no sparse-support explanation.

Erase the second-stage output with G the n×1 all-one stochastic matrix. Then QG=1 and RG=p, where p is R's row-mass vector (uniform in this family). The coupling pᵀw has rank one and is feasible; minimum stochastic cost becomes 3. Thus the observation-change monotonicity can be strict by an arbitrarily large amount. The same erasure restores feasibility in the binary impossible example. These are changes of the available observations, not a repair that preserves the original observations.

The binary arithmetic in section 4 was independently checked with exact Python Fraction arithmetic; the n-dimensional claims above follow from the displayed eigenspaces (constant vectors and their zero-sum complement).
