# Native common construction: focused primary-source audit

2026-11-02. Scope: finite relational and stochastic native realizations, observation change, prescribed-comparison lifting and latent cardinality. This is not exhaustive novelty clearance.

## Verdict

The core lift now proposed is governed by standard finite convex geometry: the linear image of a product of weighted simplices gives a Minkowski-sum feasibility polytope; relative interior characterizes exact-support lifts; separation gives dual obstruction witnesses. This applies to the actual KQ=R constraint, unlike plain Hall. Semiring factor rank transports realizations and bounds cost under matrix composition and coefficient change. Blackwell garbling already governs the two-stage chosen-model feasibility problem. Finite Strassen/Hall is a useful comparison for a simpler coupling subproblem, not the principal lift theorem here. A framework collecting these is worthwhile organization, but their restatement is not a new general realization theory. The difficult boundary is lifting *whole prescribed diagrams* while retaining native normalization, conditional structure and resource guarantees. Local liftability is not automatically joint liftability.

## Core candidate: exact constrained lift and its standard source

R. Tyrrell Rockafellar, **Convex Analysis** (Princeton University Press, 1970), Theorem 6.6, pp.48--49, states that finite-dimensional linear images commute with relative interior. Corollary 6.6.2 gives the corresponding Minkowski-sum formula. Theorem 11.3 characterizes proper separation by disjoint relative interiors; Corollary 11.6.2 characterizes relative boundary points by nonconstant supporting linear functionals. Verified against the reproduced primary book text: https://djvu.online/file/68u51YEBQaqiP . The relevant statements were checked in that primary book text.

**Application to this candidate (our explicit specialization).** Fix finite J,S,I, stochastic Q:S->I, strictly positive w_s, and allowed edges E subset J times S with every E_s nonempty. The coupling domain C_E consists of T supported within E with column sums w. It is a product over s of weighted simplices w_s Delta(E_s). Its relative interior consists exactly of T positive on every E edge. The linear map L(T)=TQ has image

    P_E = sum_s w_s conv{e_j tensor Q_s : j in E_s}.

Therefore a weakly supported lift exists iff R belongs to P_E; a lift whose support equals E exists iff R belongs to ri(P_E). This does not require injectivity of L, independence of Q rows, or distinct displayed vertices. An explicit factorization through h with no bound can always take h=S, A=T, B=identity; prescribed small h is a separate nonnegative-factorization constraint.

For independently checkable weak feasibility, minimize each linear functional over the product domain. With real vectors u_j on I, this gives

    sum_j <u_j,R_j> >= sum_s w_s min_{j in E_s}<u_j,Q_s>

for every tuple u. Necessity is immediate term by term. Sufficiency follows because a point outside the compact convex P_E has a strictly separating functional. Replacing u by -u supplies the opposite inequalities, so no missing orientation or affine-hull condition is hidden in the universal quantifier. Exact-support feasibility strengthens this to strict inequality whenever the functional is nonconstant on P_E, while retaining equality for functionals constant there. Thus the criterion does not mean strict inequality for *all* u.

**Elementary positive-coefficient proof, if desired.** For finitely many points v_l, their uniform barycenter b lies in the relative interior of their convex hull. Any relative-interior point r can be extended a small distance past r away from b while remaining in the hull: r=(1-epsilon)r'+epsilon b. Express r' as a nonnegative convex combination; adding the positive uniform contribution gives strictly positive coefficients on every listed point, including redundant points. Conversely a positive combination cannot lie in a proper exposed face, since that would force every listed point into the face. Apply this to vertices of the product of simplices and then project. This verifies the relevant finite special case without an additional regularity assumption.

**Assessment of contribution.** This is a substantive exact lift criterion, not an assumption that a lift exists; however its mathematical engine is established convex analysis. A common witness category over Bool and nonnegative reals is matrix factorization over semirings with normalization and an imposed affine constraint. Its observation-change functor is checked by multiplication, and its cost monotonicity follows because the intermediate cardinality is unchanged. These are coherent and useful synthesis but not, by themselves, a new universal factorization or optimization theorem. The exact-support criterion lifts an allowed relation E at unbounded h; it does not lift a selected Boolean factorization at its original rank, preserve a chosen optimizer, or solve the constrained NMF minimum. The main credible value is a precise integration of native witness categories, observation-change transport, and a quantitative/convex lift obstruction for the anchored problem.

## Further verified primary sources

1. Twan Koperberg, **Couplings and Matchings: Combinatorial Notes on Strassen's Theorem**, arXiv:2202.02092, Theorem 1 and Proposition 6. https://arxiv.org/pdf/2202.02092 . Theorem 1 identifies supported couplings of finite probability measures with all weighted Hall inequalities. Proposition 6 gives the deficient version: a coupling can put at least 1-epsilon mass on a relation precisely when every Hall inequality holds with additive epsilon. The paper explicitly identifies the Hall/Strassen equivalence as known and relates it to max-flow/min-cut. These supply existence and quantitative failure certificates, not only categorical packaging.

2. Derek DeSantis, Erik Skau, Duc P. Truong, Boian Alexandrov, **Factorization of Binary Matrices: Rank Relations, Uniqueness and Model Selection of Boolean Decomposition**, arXiv:2012.10496v2, Section 3, Proposition 1 and Theorem 1. https://arxiv.org/pdf/2012.10496 . Positive-entry thresholding of a nonnegative factorization gives a Boolean factorization; consequently Boolean rank is a lower bound for nonnegative rank (their statement concerns binary matrices). The same entrywise argument applies to the support of any nonnegative matrix. Do not confuse Boolean rank (OR/AND arithmetic) with binary rank (0/1 factors under ordinary arithmetic).

3. Tobias Fritz, Tomas Gonda, Paolo Perrone, Eigil Fjeldgren Rischel, **Representable Markov Categories and Comparison of Statistical Experiments in Categorical Probability**, arXiv:2010.07416v3, Section 5.1 and Theorem 5.4. https://arxiv.org/pdf/2010.07416 . In a Markov category with conditionals, informativeness via garbling is characterized by a suitable joint implementation and conditional independence/sufficiency. This is existence of a compatible joint implementation, not a property of every coupling. Later Blackwell--Sherman--Stein results impose additional representability assumptions. FinStoch has conditionals but is not itself representable; use Theorem 5.4 rather than silently importing those later hypotheses.

4. Joel E. Cohen and Uriel G. Rothblum, **Nonnegative Ranks, Decompositions, and Factorizations of Nonnegative Matrices** (1993). https://lab.rockefeller.edu/cohenje/PDFs/211CohenRothblumLAA1993.pdf . Classical baseline for nonnegative factor rank. The native stochastic factorization rank of a row-stochastic matrix equals its nonnegative rank, by normalizing the rows of the second factor and compensating the first. Zero latent rows may be deleted. The normalization argument is also given below independently.

5. The preceding audit at `../native_refinement_20261102/prior_art.md` covers matrix simulations (Esik--Maletti), bounded probabilistic minimization via invariant-subspace existential-real certificates (Kiefer--Wachter), supported probabilistic bisimulation (Jonsson--Larsen and later formulations), and Heller/Fliess positive realization. These remain controlling sources for sequential extensions; a finite response matrix alone does not enforce all continuation operators.

## Elementary transport laws (derivations, not claims of novelty)

Write factor rank over a semiring S as the least k for H=A B with intermediate free carrier S^k. A semiring homomorphism phi:S->T sends this factorization to phi(H)=phi(A)phi(B), so rank_T(phi(H)) <= rank_S(H). For nonnegative reals to Booleans use phi(r)=[r>0]: nonnegativity is essential to preserve addition. Thus Boolean-rank(supp H)<=nonnegative-rank(H). Support preserves matrix composition and Kronecker tensor. Restricting stochastic matrices gives total relations, not arbitrary relations with empty rows.

For a row-stochastic H=A B with nonnegative factors, let d=B1. Delete zero d entries (their B rows contribute nothing), set B'=diag(d)^(-1)B and A'=A diag(d). Then B'1=1 and A'1=H1=1. This proves equality of native stochastic latent cardinality and nonnegative rank for finite response tables, not sequential processes.

For any admissible stochastic input/output changes P,G, H=A B gives PHG=(PA)(BG) at the same latent cardinality. Hence r(PHG)<=r(H). If reverse admissible changes recover H from PHG, equality follows by the reverse inequality. Direct sums yield an additive upper bound and independent tensors a multiplicative upper bound by explicit block/Kronecker factorizations; equality or optimality requires separate arguments. These statements have Boolean counterparts. They transport native witnesses, not merely generated images.

A Boolean factorization can fail to lift at its chosen size for fixed numerical H. For example a strictly positive invertible n-by-n stochastic H has all-ones support of Boolean rank 1, but nonnegative rank n because ordinary rank n is a lower bound. Every individual total relation can be assigned positive row probabilities; this does not lift an arbitrary prescribed commuting diagram with fixed numerical arrows.

## Prescribed relation: independent finite lift criterion

Let mu,nu be probability laws on finite X,Y, R subset X times Y, and N(A)=R(A). A coupling gamma with margins mu,nu and support contained in R exists iff mu(A)<=nu(N(A)) for all A subset X. This is the finite Strassen theorem above. Its numerical obstruction is

  delta_R(mu,nu)=max_{A subset X}(mu(A)-nu(N(A))).

The empty subset makes delta nonnegative. Proposition 6 gives min over all couplings gamma of gamma(R-complement)=delta. This is an exact mismatch cost, not a bound on minimum latent state count.

**Exact support qualification.** Strassen alone gives support contained in R, not equality. A useful derived finite test for equality is: Hall holds and each edge (x,y) in R has mu(x)>0, nu(y)>0 and no Hall-tight A with x outside A and y in N(A). To prove sufficiency for an edge reserve epsilon at (x,y). Subtract epsilon from those two marginals. The only inequalities made harder have x outside A and y in N(A); finitely many positive slacks permit a positive epsilon, while endpoint positivity permits the subtraction. Apply Hall to residual equal-total finite measures (normalize if needed), then restore the edge mass. Necessity follows because a Hall-tight A fills all mass in N(A) from A, forbidding incoming positive mass from outside A. Average these edge-positive feasible couplings over the finite edges to obtain support exactly R. Empty-relation boundary with positive total mass is excluded by Hall itself. This proof is elementary flow reasoning; no novelty claim.

## Coherent composition that is actually available

For couplings gamma on X times Y and eta on Y times Z sharing marginal nu, their relatively independent gluing is

  omega(x,y,z)=gamma(x,y)eta(y,z)/nu(y)

when nu(y)>0, and zero otherwise. Its XZ marginal is a coupling supported in R;S when the factors are supported in R,S. Iterating this Markov gluing is associative at the level of the resulting chain joint law (products of transition kernels); it does not preserve an arbitrary preexisting three-way correlation. Exact support composes when positive supports are tracked and zero-marginal vertices removed. Marginalizing the glue can identify witnesses and does not preserve witness multiplicity.

This establishes useful relational-to-stochastic lifting for compatible boundary laws. It does NOT prove that all independently lifted squares, all shared latent constraints, or all sequential fine/coarse systems glue. A statewise supported-coupling fixed point is a valid sufficient-and-necessary construction for common deterministic covers of two *fixed* finite models; it is a different problem from arbitrary native realization of their observable behavior.

## Relevance to the previous two-stage theorem

The prior feasible polytope KQ=R, 1^T K=w^T is an additional conditional-independence constraint, not just a transportation polytope. Its reversed experiments satisfy E=D L exactly when feasible; this is Blackwell garbling. Hall tests can govern a prescribed support coupling subproblem, but are not a replacement for KQ=R when Q is genuinely stochastic. Full-support Q,R may still make the equations infeasible. The optimization min nonnegative-rank(K) over this polytope is not supplied by ordinary max flow.

## Claim discipline for the next construction

A cost-indexed category/fibration of native witnesses can organize all the above, but generic categorical definitions give only conditional transport: if a witness-transforming functor exists, costs bounded by its rule transport. The substantive result must construct that transform from independently checkable conditions in each doctrine. Do not assume cartesian lifts or exactness and then advertise their existence as proved. Separate (i) unconditional forward observation garbling, (ii) partial reverse lifts with quantitative criteria, (iii) cost bounds for explicit lifts, and (iv) optimality, which is harder and often noncanonical. No source in this bounded pass proves a universal arbitrary-stream primitive/interface discovery theorem, nor does the absence of one here establish novelty.
