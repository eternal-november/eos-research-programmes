# Discovery from incomplete transition moments

Status: written proofs with independent AI review and finite checks, 29 October 2026. These proofs use standard finite-state function algebras and stochastic partition refinement. The contribution sought is their data-to-discovery integration and the exact higher-order uncertainty obstruction, not invention of invariant-subspace methods.

## 1. Scope and the information promise

Let X={-1,+1}^n be the observed state alphabet and U a finite action alphabet. No component partition, coordinate pairing, hidden source frame, or local update coefficients are supplied. The current observed vector is assumed to be a controlled Markov state: a world is a fixed stochastic kernel K_u(x,y). It need not factor into independent coordinate mechanisms. Arbitrary nonlinear, correlated fresh hidden influences can be integrated into K. Arbitrary persistent hidden memory that makes X non-Markov is NOT covered by this identification promise.

Let chi_S(x)=product_{j in S} x_j. Fix measured feature space V_d=span{chi_S:|S|<=d}; more generally any supplied sparse-monomial span V containing 1 works. Assume only for these measured next features that

  T_u chi_S(x) := sum_y K_u(x,y) chi_S(y)
              = sum_{|R|<=k} beta_{u,S,R} chi_R(x).

The supports and coefficients beta are unknown. This is a low-degree conditional-moment promise, not a promise of low-order independence or a factorization of the whole kernel. Higher-order output couplings are unrestricted. Its force must be stated: it identifies the relevant global conditional functions from low-order readouts. Failure of this class promise invalidates extrapolation beyond the observed conditional laws.

For each action u, training supplies population mixed moments

  G_u[R,Q]=E[chi_R(X)chi_Q(X)|u],
  h_{u,S}[R]=E[chi_R(X)chi_S(Y)|u]

for |R|,|Q|<=k, |S|<=d, where the conditional response really is K_u and G_u is positive definite. Actions may be randomized or selected by an observed-state policy; no unobserved action confounding may alter the conditional response. G uses at most 2k simultaneous current coordinates; h uses at most k current and d next coordinates. Complete current-state enumeration is unnecessary. Full support of the current-state distribution suffices for G>0 but is stronger than necessary. Small eigenvalues cause statistical ill conditioning.

Regression gives beta_{u,S}=G_u^{-1}h_{u,S}, exactly. Proof: substitute the polynomial response into h and use the defining Gram matrix. Therefore the operator T_u restricted to V_d is learned with polynomially many moments for fixed d,k, without knowing any partition or constructing 2^n rows. The algebraic cost is polynomial in M_k=sum_{j<=k} binom(n,j), M_d, and |U|. This is a population theorem; finite data require concentration and inverse-conditioning bounds.

## 2. A coupled positive world family determined by those readouts

Write g_{u,S}=T_u chi_S for the learned functions. The maximal moment-compatible family is

  C(g)={fixed stochastic kernels K: sum_y K_u(x,y)chi_S(y)=g_{u,S}(x)
                  for every x,u and |S|<=d}.

This is a family of positive joint response laws, not independent intervals for separate next-coordinate marginals. Within a row, all measured moments must arise from the SAME distribution on y. Across visits the SAME kernel is used. The family is nonempty because the declared true world supplies a witness. Nonemptiness need not be efficiently decidable for arbitrary proposed g; do not count existence of a polynomial-size check without an additional representation theorem.

All members have the same learned transition action on V_d. Their higher-order joint effects can differ. For the necessity/obstruction theorem below assume C(g) contains a strictly positive kernel K^0: every row/outcome entry is positive. A numeric lower bound is not needed for the exact existence theorem, but is needed for quantitative perturbation sizes or statistical guarantees.

A proper task quotient is a map q:X->Q with |Q|<|X| such that the supplied task h factors through q and, for each K in C(g) and action u, q_*K_u(x,-) depends only on q(x). The reduced kernel is initially allowed to depend on K. This avoids conflating a common architecture with an identified mechanism.

## 3. Why unobserved joint moments matter

Lemma (invisible row perturbation). If f:X->R is outside V_d, there is a real signed vector v on X with sum_y v(y)chi_S(y)=0 for every |S|<=d but sum_y v(y)f(y) !=0. Because 1 is measured, sum_y v(y)=0. This is finite-dimensional separation, equivalently projection of f onto V_d's orthogonal complement.

For any row (x,u), K^0_u(x,-)+epsilon v remains stochastic and positive for sufficiently small nonzero epsilon and preserves every measured conditional moment. Every other row can be left unchanged. Thus the perturbation is one alternative fixed world with exactly the same conditional low-order response observations. For a fixed supplied current-state design distribution, all supplied mixed moments also agree. If the current law must itself be stationary, use the balanced construction below rather than a single-row perturbation.

Theorem (proper robust quotients must be measured algebras). If q is a proper quotient valid for every K in C(g), its full function algebra A_q={F o q} is contained in V_d. Proof: choose two distinct current states x,x' in the same q block, which exist because q is proper. If any next q-block indicator f lies outside V_d, perturb only row x by the preceding lemma. Either K^0 already violates q-closure or the perturbed world does, since its f expectation changes at x and not x'. Contradiction. Block indicators span A_q.

Consequently every proper robust quotient in this maximal family has not only common architecture but IDENTIFIED reduced dynamics: T_u is already fixed on A_q. A proper quotient with world-dependent reduced law is impossible in this particular rowwise-complete family. Such uncertainty is possible in smaller families with cross-row parameter constraints; it must not be silently excluded in a general theorem.

Stationary refinement (one action). Suppose K^0 has a strictly positive stationary law pi and x,x' lie in the same non-singleton q block. Perturb row x by epsilon v and row x' by -epsilon pi(x)/pi(x') v. The weighted row changes cancel, so pi remains stationary; normalization, all measured conditional moments, and positivity for sufficiently small epsilon are preserved. The difference of next-block probabilities changes by epsilon(1+pi(x)/pi(x'))<v,f>. Thus either the base world or the perturbed world violates q, while BOTH have the same stationary current law and all supplied one-step mixed moments. This is not equivalence of arbitrary longer histories. For controlled stationary data, an analogous balance must include the actual action-selection weights; no unqualified common stationary law for every action is asserted.

Resolution corollary. Every proper robust quotient has at most 2^d blocks, independently of n. A nonzero multilinear polynomial of degree at most d on the n-cube is nonzero on at least 2^(n-d) states. To prove this, write f=g+x_n h. If h=0, induct on n and double the support. If h is nonzero, its degree is at most d-1; on each point where h is nonzero at least one of g+h,g-h is nonzero, giving the bound by induction. Each nonempty quotient-block indicator lies in V_d, so each block contains at least 2^(n-d) states. Their disjoint supports give |Q|<=2^d. The bound is sharp: projection to d raw coordinates has block indicators of degree d and is a valid quotient, for example for an IID uniform kernel. For d=n the bound is vacuous. This bound concerns the maximal moment-compatible family; extra structure can exceed it.

This is the essential crossing obstruction. Knowing each separate component's moments does not certify their joint quotient. Products of their observables belong to the joint algebra and may leave V_d. One cannot stop at linear invariant-span tests.

## 4. Constructive discovery or an obstruction

Let A_0 be the unital pointwise algebra generated by the task's block indicators. Iterate:

1. If A_j is not contained in V_d, report that no proper robust task quotient exists in C(g).
2. Otherwise apply each learned T_u to a basis of A_j.
3. Let A_{j+1} be the unital pointwise algebra generated by A_j and these images.
4. Stop when A_{j+1}=A_j.

All equalities are equalities of functions on the Boolean cube. Sparse Walsh polynomials make them exact by reducing products with x_i^2=1. During algebra generation, an outside-V_d monomial component can be detected immediately. It is unnecessary to build the entire outside algebra.

Theorem. If this process stabilizes inside V_d, its atom partition q_* is the unique coarsest proper robust task quotient, unless it is the identity. Every K in C(g) has the same induced controlled kernel on q_*. If the process exits V_d, no proper robust task quotient exists. The identity remains a vacuous quotient when X is assumed Markov; it is not counted as useful success.

Proof. Every robust proper quotient's algebra contains the task algebra and lies in V_d by Section 3. Its closure under all K implies closure under learned T_u, and its function algebra is closed under products. Induction gives A_j subset A_q. Thus an exit rules out every proper robust task quotient. At stabilization, T_u A_* subset A_* is exactly the finite-state lumpability criterion. The task factors through its atoms. Inclusion A_* subset A_q proves coarseness. Since A_* subset V_d, all induced expectations, hence the entire quotient kernel, are data identified. Positivity follows by pushing forward any compatible K.

The dimension can strictly increase at most dim(V_d) times before stabilization or exit. Arithmetic-operation count is polynomial in the maintained sparse polynomial and algebra representations, for fixed d,k. Bit complexity also depends on coefficient bitlength, exact field operations, and the representation of the supplied task indicators; those costs are not bounded here. Intermediate products have degree at most twice the current feature degree; reduce them and stop if they leave V_d. No 2^n transition table is constructed.

Represent the quotient by the tuple of a basis f_1,...,f_r of A_* evaluated on x. A finite real function algebra of dimension r has exactly r atoms, so this is an r-state quotient even if it is left in symbolic coordinates. Primitive idempotents and stochastic rows can be extracted from the r-dimensional multiplication algebra, with exact algebraic-number handling charged. When r grows exponentially, the result does not promise an inexpensive explicit quotient table.

The result is strongest when r is small. It does not itself discover a physically available readout interface: evaluating its sparse polynomials requires the indicated sensor coordinates. Those supports and operation costs must be charged.

## 5. Obstruction certificates and experiment design

An exit certificate is a finite derivation from task indicators by transition images and pointwise products, ending in f outside V_d. This certifies no proper robust quotient, under the positive-interior premise. For a particular proposed q, a block indicator outside V_d gives the signed row perturbation above and two data-equivalent worlds that disagree on q-closure if one valid world is available. Otherwise one obtains a direct invalid-world witness, not necessarily a valid/invalid pair.

A new measured next observable e can eliminate a particular invisible contrast v precisely when <v,e> is nonzero. Adding its conditional moment to the observation vocabulary shrinks the world family, but need not eliminate every other obstruction. Feasibility and availability of that experiment are separate conditions. Measuring a single unconditioned average need not constrain the problematic conditional row.

No claim of all-transcript equivalence is made merely from low-order one-step moment equivalence. The experiment is the declared collection of mixed population moments. If arbitrary high-order/time-aligned readouts are permitted, the two worlds may be distinguishable. The exact evidence protocol must remain fixed.

## 6. Why this does not automatically prove the growing parity family

If m discovered component coordinates each use two raw bits, their joint block indicators can have Walsh degree 2m. Fixed d cannot certify the full joint quotient against all arbitrary higher-order couplings in C(g). This is a theorem-level obstruction, not a numerical inconvenience.

The proposed growing paired-parity family can cross this barrier only through additional learned/structural information: known independent output-bit noise plus deconvolved extremal parity equations force all pre-noise quotient outputs simultaneously to equal their learned nonlinear Boolean functions on realized support. Disjoint learned sensor pairs then yield independent parity-noise channels. That proves the whole joint quotient law from bounded-order data without measuring degree-2m moments. It uses positivity at an extremal face and the declared noise factorization, and must be presented as a separate mechanism, not a consequence of the arbitrary-coupling theorem alone.

Persistent hidden nuisance is compatible with that pathwise cancellation argument on the covered realized histories. Extrapolation to hidden modes never reached in training is not justified by extremal averages alone. A stronger pointwise structural promise or a support-transfer condition is needed for that deployment claim.

## 7. Exact whole-system witness and its interface cost

For each surviving K, choose a set-theoretic fiber encoding x<->(q(x),r(x)). Fibers need not have equal cardinalities. Then

  K_u(x,x') = Kbar_u(q(x),q(x')) R^K_u(r(x') | q(x'),x),

where R is the conditional remainder law; on zero-probability quotient transitions choose an arbitrary distribution on the appropriate fiber. This is an exact positive two-stage realization: draw the quotient update using q and u, then draw the remainder using the old WHOLE x and the sampled new q. It preserves the joint transition and every resulting controlled trajectory for the same initial law.

The first stage's incoming interface is the action plus the discovered q state; its evaluation requires the measured raw coordinates appearing in q's sparse formulas. The remainder may require all old fine-state information. This is not a free physical encapsulation/replacement theorem, and no bounded outgoing interface or cheap implementation of R follows. The coherent decomposition retains the same fixed K in R throughout time. Independently switching remainders or worlds per step is not justified by data ambiguity.

For two discovered quotients, their joint realization as ONE autonomous quotient requires closure of the algebra generated by BOTH quotient algebras. Separate closure of each does not suffice. The same algorithm either constructs the coarsest task refinement of their combined information or emits the higher-order obstruction. The corresponding whole-system remainder is then formed once from that joint quotient; it is not the product of separately conditioned remainders.

## 8. A fixed-size discovered core in an arbitrarily large nonlinear whole

Here is a nonextremal observed-law family compatible with the theorem itself. It is distinct from the stronger growing-core paired-parity family.

There are n observed sign bits, n>=4. One bit a is the task readout. Two other positions i,j are unknown; write b=x_i x_j only for constructing the example. Let F(a,b) be any nonlinear sign-valued Boolean function of a,b whose real polynomial includes the ab term (for example the sign encoding of Boolean AND). Before independent output-bit flips of probability eta in (0,1/2), define

  a_next=b,
  x_i_next=R,
  x_j_next=R F(a,b).

The shared sign R and every other nuisance update may be correlated and nonlinear. For a concrete bounded-degree family valid for every n, choose a fresh sign Z with an arbitrary fixed bias strictly between zero and one, independent of the past, and set R=Z r(x), where r is one current Walsh monomial of degree at most two. Each other nuisance pre-noise output is R m_l(x), where m_l is an arbitrary current monomial of degree at most two. The choices r,m_l and the Z bias need not be given to the learner. These are nonlinear interacting updates through a common disturbance; they are not arbitrary persistent hidden-memory updates. Different nuisance constructions remain possible. Independent output-bit noise ensures every full transition entry is positive; eta is needed only for constructing this witness, not supplied to the moment-regression learner.

Write rho=1-2eta. Irrespective of the shared R law,

  T a = rho b,
  T b = rho^2 F(a,b),
  T(ab)=rho^3 b F(a,b).

All lie in A=span{1,a,b,ab}. The learner starts with task a and observes low-order mixed moments, with d=3 and k=9. This fixed bound follows explicitly: a measured product contains at most three pre-noise outputs. If it contains a, the remaining at most two R factors cancel or leave one R, and its current degree is at most seven. If it contains three R-carrying outputs, the residual R contributes at most degree two, the unique F contributes at most degree three, and the other two monomials at most four, totaling at most nine. Without F the bound is at most eight. Independent output noise multiplies a measured product by rho to the product size and does not increase current degree. If Z is fair, odd-R moments vanish and k=7 suffices. For n<9, k is naturally truncated at n. It is not given i,j,b,F or eta. Regression of T a reveals the nonzero monomial b and its coefficient. Pointwise multiplication introduces ab. Subsequent learned transition images certify A's closure. Thus the algorithm discovers a four-state quotient from n raw bits and the unknown composite parity, with no supplied partition.

Coarseness is immediate: any task-preserving quotient must preserve a; because rho!=0, closure under T a forces b as well. Conversely the displayed four-dimensional algebra closes. Hence four states are necessary and sufficient. For n>=4, this is a strict reduction from 2^n states. Other whole-mechanism coefficients and coupled higher-order response laws remain unresolved, but the quotient dynamics are identified by the measured transition action.

This construction does not rely on data being at an extremal observed probability: eta>0 makes quotient probabilities interior. Its cancellation is not handed to the learner as an invariant; it is inferred from the learned conditional transition operator. The declared low-degree conditional-moment class and informative Gram matrix are still strong assumptions. The physical shared-source construction is one witness inside the larger Markov moment family, not an identified physical ontology.

A direct nonlinear gate computation implements the discovered q=(a,x_i x_j); it uses three sensor coordinates and one multiplication/XOR. The whole-system remainder has n-2 bits under a chosen parity-fiber encoding and can remain highly coupled. The example therefore demonstrates cheap task-component discovery and an explicit interface, not cheap reconstruction of that remainder.

## 9. Incoming action interface

For finite U, the coarsest memoryless action summary is the equivalence u~v iff T_u f=T_v f for every f in the discovered quotient algebra. These are equalities of learned sparse functions. Choosing a basis suffices. The quotient kernel factors through this action summary, and any summary giving identical quotient responses must refine it. If actions are supplied as Boolean input coordinates, regression may instead use joint current/action Walsh features under a sufficiently informative design. A coordinate is essential to the quotient response exactly when the discrete derivative in that coordinate of some transition-basis function is nonzero; exact sparse coefficients decide this without a whole transition table. This discovers input dependence under the declared action vocabulary, not arbitrary physical sensor or actuator synthesis. Summarizing action histories with memory requires a separately supplied timing/register model and is not proved here.

## 10. Passive stationary population-law check

The exact rational regression check also generates one-step readout moments under the positive 16-state fixture's own stationary law, without state preparation. That law is nonuniform: total variation from uniform is approximately 0.1295854 and minimum state mass approximately 0.0418029. The learner receives only the current-feature Gram matrix and current/next mixed moments, not the stationary state probabilities, whole transition matrix, source law, coordinate pairing, or eta. Exact Gram inversion recovers precisely the same transition polynomials and four-state quotient as the uniform-design check. The smallest Gram eigenvalue is approximately 0.6688468. The whole matrix and stationary distribution are bounded test-oracle machinery, not inputs to the learner and not an algorithm proposed for large systems. These are population probabilities, not finite sampled trajectories or an empirical mixing-time guarantee.
