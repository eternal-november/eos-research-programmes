# Obstruction and experiment certificates under coupled uncertainty

## Purpose and scope

This module addresses a narrow but necessary part of decomposition discovery: how to certify a proposed component across unresolved mechanisms, how to produce two indistinguishable mechanisms that disagree about it, and which additional tests can resolve that disagreement. It does not independently supply an architecture learner. The elementary linear-programming ingredients are standard; the contribution sought by the research programme must come from deriving this compact representation from readouts and using it for unsupplied decomposition discovery.

The distinction between a valid component and a known component law is essential. A partition can define a legitimate quotient in every compatible world while the quotient's transition probabilities remain unidentified. Conversely, an observed process may have a simple predictive model without defining an autonomous subsystem pointwise in the hidden state.

## 1. Explicit finite-dimensional uncertainty contract

Let theta in R^d specify one complete mechanism choice, fixed across every component, context, and time. Suppose the evidence and model promises yield a nonempty compact rational polytope

P = {theta : A theta = b, G theta <= h}.

Positivity and normalization constraints on every admitted local kernel belong in this same P. Shared parameters must not be replaced by independently chosen row intervals. The statement below presupposes that all parameters in P admit positive joint realizations, or that an exact positive-realization filter has already been included. It is unsound to interpret arbitrary local feasibility as a whole-system realization.

A supplied local kernel representation has entries affine in theta, with arbitrary dependence on its finite state and input indices. The local mechanisms can therefore be nonlinear in those indices. For a proposed partition q, admitted interface r, and next quotient block B, equality of the relevant aggregated rows is a finite list

C_q theta = d_q.

The list compares all old states identified by q and all environment contexts identified by r. In particular, if the component claims independence of a hidden exterior variable, its contexts must be compared at the same retained state, not merely averaged under an observational distribution.

This linear contract is not automatically obtained from trajectory data. With a fixed theta reused across time, length-L trajectory probabilities are generally polynomial in theta. Linear evidence constraints require a justified conditional-table access regime, known experimental occupancies, an explicit affine mixture-law representation, or another valid reduction. Replacing a polynomial fixed-world law by independent per-time parameters changes the problem. If P is merely an outer approximation, universal certificates remain sound for its represented worlds, but a counterexample in P need not correspond to a data-compatible world. Indistinguishable-world claims require exact membership and realization.

## 2. Three different questions and finite certificates

Write Z_q = {theta : C_q theta = d_q}.

**Uniform quotient validity:** q is valid across the evidence if P is a subset of Z_q. For each row c of C_q, compute the minimum and maximum of c theta - d over P. Validity holds exactly when both extrema are zero for every row. A nonzero extremizer is a single fixed-world counterexample to uniform validity. It need not show that q is valid in any other world.

**Ambiguous quotient validity:** the evidence admits both a world in which q is valid and one in which it is not precisely when P intersect Z_q is nonempty and P is not a subset of Z_q. One feasibility solve returns theta_good; one nonzero contrast extremizer returns theta_bad. Both satisfy the same evidence equations and all coupled physical promises. This is a constructive two-world obstruction, not merely a statement that the data are incomplete.

**Uniform invalidity:** if P intersect Z_q is empty, no admitted world realizes that candidate. A rational Farkas certificate of infeasibility is checkable without searching for an alternative world. This conclusion concerns this candidate only, not every possible partition or interface.

**World-invariant quotient dynamics:** if q is uniformly valid, choose one representative per retained context and write the induced kernel as m_q(theta)=M_q theta + a_q. Its law is identified exactly when every row of M_q is constant over P. Otherwise two extrema give different valid quotient mechanisms with identical evidence. Thus uniform validity does not imply a unique controller-relevant stochastic law.

The LP size depends on the explicit compact description of P and on the number of local contrast rows. It does not intrinsically depend on the global state count. This is only useful when the preceding identification/decomposition steps produce such a compact description and bounded local contrast tables. It is not a polynomial bound for discovering P, choosing q, positive stochastic realization, or arbitrary hidden architecture inference.

## 3. Certificate verification, including boundary faces

For rational input, an LP optimum and matching dual witness certify each bound. If the primal maximum of c theta is U, a dual witness consists of unrestricted lambda and nonnegative mu with

A^T lambda + G^T mu = c,

b^T lambda + h^T mu = U.

Checking the displayed identity, mu>=0, primal feasibility, and equality of objective values proves optimality. Repeat with -c for a lower bound. To certify c theta=d throughout P, provide both upper d and lower d witnesses. Strong duality applies to the nonempty compact feasible polytope. Degeneracy does not invalidate this method.

Equivalently let V = span(P-P), the direction space of the affine hull. A linear functional is identified iff it annihilates V. The inequalities may force a lower-dimensional face, so ker(A) alone is generally too large. One must compute the actual affine hull or keep the LP formulation. For example, theta_1,theta_2>=0 and theta_1+theta_2<=0 force both coordinates to zero, even though A may be empty.

Rational certificate size is polynomially bounded in the rational LP input size under the usual encoding. This does not make the input representation or the physical witness cheap. A certificate must retain the same theta throughout; separate optimizers for different rows are tests of universal validity, not a joint fitted world.

## 4. What additional experiments identify

Suppose a permitted collection of experiments has exact mean readouts E theta+e. The source law, intervention semantics, and exclusion conditions that justify this map must be part of the declared model, not inferred from randomization alone.

Two named worlds theta_1,theta_2 are separated by this experiment iff E(theta_1-theta_2) is nonzero. If every permitted experiment has the same law in the two worlds, no adaptive policy restricted to those experiments can distinguish them, provided equality is conditional on every attainable experimental history and the same initialization. Equality of isolated unconditional means alone does not imply adaptive indistinguishability.

A vector functional F theta is recoverable from these exact experiment values throughout P iff

ker(E) intersect V is a subset of ker(F).

Equivalently, on the affine hull, F factors through E. A checkable linear certificate is F = T E + N with every row of N annihilating V. Then, for a fixed theta_0 in P,

F theta = F theta_0 + T E(theta-theta_0).

Necessity follows by taking a relative-interior point theta_0 of P. If v lies in V, E v=0, and F v is nonzero, then theta_0 plus or minus a sufficiently small multiple of v remains in P. Those two positive feasible worlds have equal experiment values and differing F values. This is a constructive obstruction once a relative-interior point and feasible step size are provided.

Applying F=C_q identifies the actual closure contrasts. Applying F=M_q identifies the quotient law after closure. These are distinct experimental objectives. The vector criterion is sufficient to decide whether C_q theta=d_q, but need not be necessary for the Boolean validity question: a candidate may be invalid throughout P even while its violation magnitude is unidentifiable. If a valid point lies in relint(P), then a direction v in ker(E) intersect V with C_q v nonzero produces an observationally indistinguishable valid/invalid pair, making the criterion necessary for deciding validity in that setting. Boundary-only valid points require a one-sided feasible-direction analysis, or an explicit two-world feasibility test.

Selecting a minimum-cost subset of experiment rows is a separate combinatorial problem. Even when checking a selected row family is linear algebra, optimal test selection must not be advertised as cheap without an additional theorem. A greedy rank-increasing choice supplies a finite sufficient family whenever available experiment rows span the needed directions, but not necessarily minimum cost.

## 5. A complete-passive-history counterexample

Let the latent state be (a,b) in {0,1}^2. Only a is observed. Choose any p_0,p_1 strictly between zero and one and a bound t smaller than min(p_0,p_1,1-p_0,1-p_1). For one fixed theta in [-t,t], set

P_theta(a'=1 | a,b) = p_a + theta(2b-1),

P_theta(b'=0 | a,b,a') = P_theta(b'=1 | a,b,a') = 1/2.

The resulting four-state kernel is strictly positive. Initialize b_0 as a fair bit independent of a_0. At every time b_t is fair and independent of the entire observed a-history through t. Therefore the complete passive observed process a_t has transition probability p_a for every theta. This is exact equality of all finite passive trajectory laws, not just matching low-order moments.

At theta=0, q(a,b)=a is a pointwise autonomous quotient. At theta!=0, the two states (a,0) and (a,1) have different next-a probabilities, so q is not pointwise autonomous. Nevertheless, the passive a-process remains Markov with the same law. A predictive state representation alone cannot certify that a is an autonomous physical component under changes to the hidden-bit mechanism.

If an allowed intervention sets b=1 or b=0 without changing the update equation, the difference in next-a probabilities is 2theta, so the ambiguity is resolved. If b cannot be intervened upon or measured and experiments act only through p_a in a way preserving fresh fair b, the ambiguity persists. Such an intervention is not assumed to be physically available merely because it exists mathematically.

This example is an obstruction calibration, not the positive validation family requested by the programme. It deliberately demonstrates that observational task simplification and pointwise subsystem decomposition are different targets. The positive discovery theorem must supply structural restrictions under which hidden directions do not invalidate the discovered component, and must state how those restrictions are evidenced or promised.

## 6. Refinement caution

A violated equality between two distinct old states can sometimes be repaired by separating those states. Therefore a single failed quotient is not a certificate that no finer useful quotient exists. By contrast, if a proposed next block has a nonzero hidden-context response at one fixed old state and fixed retained interface value, any finer next partition whose blocks are all autonomous would sum to an autonomous coarse block, a contradiction. This latter failure can rule out every deterministic refinement preserving that output block under the same interface contract.

Similarly, an empty feasible parameter set for a particular partition does not exclude another partition. A global impossibility statement needs an exhaustive symbolic argument, a sound coarsest-refinement theorem, or a search certificate covering the allowed architecture universe.

## 7. Operational indistinguishability and statistical qualifications

The hidden-bit example extends to every history-adapted controller whose allowed action u changes the known p_a to p_(a,u) but does not measure or bias the freshly fair b. Conditional on the observed history and chosen action, averaging b still gives p_(a,u) in every world. Induction proves equal action/readout transcript laws under the same randomized controller. Consequently, the failure of pointwise autonomy does not itself imply a difference for a task expressible solely through that permitted transcript. The stronger physical claim concerns stability under a larger declared family of exterior changes. That family must be stated rather than justified by the word 'component'.

For a permitted bounded observation Y in [0,1] with known candidate means differing by Delta>0, a midpoint test based on N independent trials has error at most 2 exp(-N Delta^2/2). Thus N >= 2 log(2/alpha)/Delta^2 is a sufficient conservative count for choosing between those two candidate means with error at most alpha. This is a two-world test, not recovery of an arbitrary mechanism family. Experiment cost, access and independent resets remain separate assumptions.

For a recovered linear factor F = T E + N on the feasible affine hull, observational error eta propagates to functional error at most ||T|| eta in compatible norms. A tiny effective singular value can make the exact row-space criterion statistically useless. Exact satisfaction of a closure equality cannot be inferred uniformly from finitely many noisy samples without a separation promise or a one-sided relaxation.

If evidence yields only a confidence outer polytope P_hat, a universal statement valid throughout P_hat is a valid confidence-qualified conclusion whenever the true world belongs to P_hat. A pair drawn from P_hat may be merely statistically compatible, not exactly observationally indistinguishable. The certificate must name which interpretation is being used. Extra points introduced by a computational relaxation are not automatically physical counterexamples.
