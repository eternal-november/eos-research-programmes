# Discovering exterior-independent local mechanisms by regime separation

28 October 2026. Research theorem note. These are explicit closure and composition results for the subsystem-discovery programme, not a general certificate of physical-world membership. The linear algebra and causal composition mechanisms are established principles; no priority claim is made.

## Main point

Observed invariance across environmental regimes is not sufficient by itself. Hidden effects can cancel in the regime averages. If the experimental regimes separate all relevant hidden effect directions **after conditioning on the proposed local state and boundary**, invariance instead implies that the local response is independent of each hidden effect individually. This pointwise conclusion survives new history-dependent environmental behaviour, rather than only mixtures of the original regimes.

The exterior may have arbitrarily many internal states. What is bounded is its space of effects on the local transition being tested. No reconstruction of the exterior architecture is required. Discovering the local state, candidate boundary grammar, and valid regime-separation assumptions remains the separate burden of the main discovery theorem.

## 1. Conditional mechanism and regime experiments

Let c denote a proposed local condition: an internal local state, permitted incoming boundary values or a bounded boundary-history summary, and an action if actions are present. Let Y be the full local next-step outcome being preserved, including any outgoing message whose correlation with the next state matters.

For each c there is a finite hidden exterior-effect alphabet Z_c, of size r_c. It need not be the exterior state alphabet. Many exterior states and histories can have the same effect. The physical local response under this description is a stochastic row

    K_c(z, y) = P(Y=y | c, hidden exterior effect z).

This mechanism is held fixed across the declared regime interventions. Changes of the local mechanism itself are not covered. Regime e changes the conditional effect distribution M_c(e,z), giving the identified local row

    L_c(e,y) = sum_z M_c(e,z) K_c(z,y).

Every row of M_c is stochastic. Crucially, this equation uses the conditional effect distribution given c, not an unconditional stationary distribution of the exterior. Feedback, selection, and conditioning can change the rank.

The condition c must contain every retained aspect of the local past on which K depends. Unbounded hidden local memory cannot be excluded by a finite window test. A declared memory/effect-space bound, or an independently justified finite sufficient representation, is necessary.

## 2. Exact closure and its converse obstruction

**Theorem 1.** Suppose M_c has full column rank. Then the following are equivalent:

1. Every regime has the same local row L_c(e,.)=k_c.
2. Every hidden effect has the same local row K_c(z,.)=k_c.

Proof. A left inverse A_c M_c=I exists. Since M_c 1=1, A_c 1=1. Therefore

    K_c - 1 k_c = A_c (L_c - 1 k_c).

One direction follows from this identity and the other by taking mixtures. QED.

Thus invariance establishes closure against arbitrary changes in the effect distribution: point masses, new mixtures, correlations with past local outcomes, and adversarial history-dependent choices are all allowed. This does not allow new effect modes outside Z_c, a changed local mechanism, or a new causal channel bypassing the candidate description.

**Rank-deficiency obstruction.** If M has a nonzero null vector v, choose a strictly positive outcome row p and a nonzero zero-sum vector d. For sufficiently small epsilon,

    K(z,.) = p + epsilon v_z d

is stochastic and strictly positive. Every observed regime gives L(e,.)=p, although K is not constant. The null vector cannot be a nonzero constant because M1=1. A new exterior distribution w with wv!=0 changes the local row. Consequently rank deficiency permits a genuinely invisible residual influence.

This is an observational impossibility, not merely a defect of a particular estimator. Let the exterior resample z independently each tick from the tested regime distribution and let the local outcome use K(z,.). All tested local histories are then IID p, identical to an autonomous local generator, while an untested exterior change can distinguish them. Positive transition probabilities and arbitrarily long tested records do not resolve this ambiguity.

### Unconditional rank is insufficient

Let the observed condition C be binary. In every regime take P(Z=1|C=0)=.2 and P(Z=1|C=1)=.8, but vary P_e(C=1) between .2 and .8. The unconditional Z distributions have probabilities .32 and .68, so their two-row mixture matrix has full rank. For each fixed C, however, the conditional mixture rows are identical and have rank one. Hidden response contrasts can therefore cancel after conditioning. An unconditional rank calculation does not validate Theorem 1.

## 3. A lower-dimensional effect-space version

The finite mode alphabet can be replaced by a linear space V_c of bounded real functions of the exterior state/history. Assume V_c contains constants and all transition-probability functions z -> K_c(z,y). Let T_c:V_c -> R^E map a function to its expectation in each conditional experimental regime.

If T_c is injective, equality T_c K_y=k_y 1 implies K_y=k_y pointwise on the modeled exterior states. The proof is injectivity applied to K_y-k_y. Thus the relevant complexity can be the dimension of the local effect space, rather than the exterior state count. The space and injectivity are model/experiment requirements; observing a few invariant averages does not itself verify them.

## 4. Quantitative closure and finite observations

Fix a left inverse A_c and let a_c=max_z sum_e |A_c(z,e)|. For any candidate stochastic row q_c,

    max_z TV(K_c(z,.), q_c)
      <= a_c max_e TV(L_c(e,.), q_c).

This follows by applying the signed row combination above and the triangle inequality for the one-norm. If sigma_min(M_c)>=gamma, the Moore-Penrose inverse gives a_c<=sqrt(E)/gamma. This bound may be loose; the actual left-inverse row norm can be smaller.

Suppose estimated rows satisfy max_e TV(Lhat_c(e,.),L_c(e,.))<=delta_c. Fit q_c in the probability simplex to minimize max_e TV(Lhat_c(e,.),q_c), a finite linear programme, and let its fitted radius be Rhat_c. Then the uniform hidden-effect error is at most

    epsilon_c = min(1, a_c (Rhat_c + delta_c)).

The estimated average need not identify an exterior state. It identifies a local kernel with a bound holding for every modeled exterior effect. Validity of the bound still depends on the actual conditional mixture/effect-space separation promise.

For exact discrete boundary selection, suppose every false candidate has hidden-effect variation radius at least Delta and a_c<=a uniformly. Its observed regime radius is at least Delta/a. A uniform row error delta<Delta/(2a) permits a threshold between delta and Delta/a-delta that retains every exactly closed candidate and rejects every such false one. Without a gap, return approximate certificates and unresolved candidates, rather than assert exact minimality.

If local conditional rows are obtained from independent windows, standard finite-alphabet concentration plus the minimum condition probability gives delta_c. When local states are inferred through noisy sensors, their calibration and deconvolution errors must be added. Neither independent sampling nor a conditioning denominator can be assumed for an arbitrary trajectory. Uniform bounds must cover every data-selected candidate, or use separate validation data.

## 5. Boundary discovery rather than a supplied separator

Let B range over a finite declared grammar of candidate boundary subsets, bounded history summaries, and input/output timing contracts. The particular successful boundary is not supplied. For each candidate, form its local conditions c and test regime invariance.

Assume the conditional expectation operators in Section 3 are injective for the relevant omitted-effect spaces of **every candidate tested**. Then the exactly invariant candidates are exactly the causally closed candidates in this universe. Searching these candidates and applying a resource or inclusion criterion discovers a boundary. Multiple valid boundaries may remain, and need not be collapsed to a preferred physical partition.

This premise is stronger than observing invariance in the winner. It must follow from an experimental design, a model-class theorem, or a separate certificate. Defining the hidden effect space to contain only already constant functions would make the result vacuous. The main construction must specify an independently meaningful family of possible omitted influences before seeing which candidates pass.

The search need only manipulate candidate local states, boundary tables and local effect spaces. It need not enumerate the exterior's whole hidden state. Its complexity nevertheless depends on the candidate grammar, its width and memory bound, and the number/conditioning of regimes.

## 6. A concrete sufficient regime design

One sufficient source of rank, not the only one, is an exterior soft-tilt family. Suppose, for each c,

    M_c(e,z) = w_c(z) exp(theta_e s(z)) / Z_c(theta_e),

where w_c(z)>0, all r_c scores s(z) are distinct, and at least r_c regime parameters theta_e are distinct. The labels and scores need not be observed. The resulting matrix has full column rank.

Proof. Row and column scaling reduce the question to exp(theta_e s(z)). A nonzero linear combination of r distinct exponentials has at most r-1 distinct real zeros. Induct on r: divide by the exponential with smallest exponent, differentiate, and apply Rolle's theorem to the resulting r-1-term exponential sum. Therefore an r-by-r evaluation matrix at distinct theta values is nonsingular. More rows retain full column rank. QED.

If only an upper bound r_max is known, r_max distinct regimes suffice for every actual r_c<=r_max. A finite-sample theorem also needs quantitative conditioning; rank alone can become arbitrarily ill-conditioned.

This design does not expose hidden labels or reset the subsystem to its component states. It is nevertheless a substantial intervention grammar. In particular the tilt formula must hold **conditional on c**. It does not follow automatically from changing an unconditional stationary environmental distribution. Regime parameters must be part of the actual data/access protocol, not invented after passive observations have been collected.

## 7. Positive causal gluing with an unidentified exterior

Let a discovered local mechanism be a stochastic kernel

    k(dx',dv | x,a,u),

where x is local state, a is action, u an incoming boundary message, and v the outgoing message. Include all correlations to be preserved in this joint kernel. An admissible exterior may have any finite hidden state space Z and arbitrary history-dependent positive or nonnegative kernels. The causal round is:

1. The controller chooses a from its permitted observation history.
2. The exterior produces u using its state/history and the allowed past outgoing messages and actions.
3. The local mechanism draws (x',v) from k given (x,a,u).
4. The exterior updates its own hidden state using its previous state, u,a,v and its permitted history.

**Outward sufficiency is a separate premise.** Inward response closure alone does not prove that the actual exterior reads local state only through v. An original exterior could depend on private x or x' through unrecorded outward channels. The actual-whole factorization therefore needs this output restriction separately justified, or the relevant local state exposed as a charged outgoing message. The closure theorem by itself certifies a response module, not a bidirectionally isolated physical component.

The product of these normalized kernels gives a positive/nonnegative joint execution law. Iterating gives every finite history law, consistently; no exterior state identification is required. More general standard measurable-state versions follow from the usual causal kernel construction. An instantaneous circular dependency is not covered without a separate fixed-point semantics.

If the closure theorem established k pointwise for all modeled hidden exterior effects, this construction remains valid under arbitrary exterior policy changes consistent with that mechanism and boundary alphabet/timing. The new exterior need not preserve its training-regime mixture weights or stationary distribution. All uncertainty about its architecture is retained in its causal boundary process.

Different exterior realizations that induce the same conditional boundary-input law for every permitted outward history are interchangeable for every such local controller. This is a statement about causal interaction kernels, not equality of one uncontrolled marginal transcript. An exterior with a hidden state that responds differently to new actions may fail this equivalence even if training data agree.

### Adaptive robustness

Suppose the true local joint kernel, conditional on every compatible exterior state and complete past, differs from k by at most epsilon uniformly in (x,a,u). Couple the two local draws maximally while using identical exterior/controller randomization whenever their transcripts still agree. At each round disagreement probability increases by at most epsilon. Therefore H-step coupled-transcript TV is at most min(1,epsilon0+H epsilon), where epsilon0 is initial joint-law error. Adaptive choices are allowed because the bound is pointwise at each history.

Changing a sensor channel requires an additional observation error term. A physical hazard not represented in the retained outcome/trace is not certified by this bound.

## 8. Joint subsystem claims need joint audits

Two separately closed marginal responses need not form one closed joint subsystem if their fresh randomness can be coupled by the exterior. For example let Y1,Y2 be fair bits and, conditional on hidden z, set

    P(00|z)=P(11|z)=(1+rho_z)/4,
    P(01|z)=P(10|z)=(1-rho_z)/4,

with -1<rho_z<1. Both marginal responses are independent of z, while their correlation changes with z. Testing them separately proves no joint closure. Test the union outcome, retain the shared random source as part of the boundary, or use a justified independent-innovation typing promise. Sampling two inferred marginal kernels independently silently changes the model.

Likewise, if a finite summary q(x) is used instead of the local state, its joint next-summary and outgoing-message law must be constant on every q-fiber for each admitted input/action. This is controlled lumpability with the message correlation retained. It permits causal substitution into every exterior that sees only the declared messages. If the exterior receives extra private-state information, the quotient contract is no longer the same one.

## 9. Scope relative to earlier results

The earlier full-coverage product-atlas theorem learned every modeled factor from its sensor patches. Here the closure certificate can leave exterior architecture and internal states entirely unidentified, provided its possible local effects are covered by the stated regime-separation condition. This changes both the access assumptions and the target. It is not a strict extension on identical passive data.

The main discovery task still has to construct useful local states and candidate boundaries from readouts, establish a nontrivial family satisfying the intervention/effect-space assumptions, and charge all experiment, observation, communication and memory resources. The present note supplies the exact exterior quantifiers, robustness implication, causal witnesses and explicit impossibility cases. It is not itself the entire subsystem-discovery theorem.

## 10. Why an unknown exterior memory bound cannot be tested away

Fix any integer k>=1 and 0<delta<1/2. Compare iid fair binary readings with the stationary order-k process

    P(O_{t+1}=O_{t-k+1} | O_{t-k+1},...,O_t) = 1/2+delta.

Take the initial k-bit history uniformly distributed. For any target k-word (b_1,...,b_k), the two possible predecessor words are (0,b_1,...,b_{k-1}) and (1,b_1,...,b_{k-1}); their transition probabilities into the target sum to 1. Thus the uniform k-word distribution is stationary. Every consecutive window of length at most k has exactly the iid fair distribution. At length k+1 the first and last bits agree with probability 1/2+delta rather than 1/2.

This is a finite hidden exterior realization: a k-bit shift register with strictly positive next-bit probabilities. Therefore checking any fixed finite collection of consecutive window laws cannot certify that a small fitted local state is sufficient against exterior memories of unbounded size. For windows with arbitrary fixed lags, choosing k larger than their total span gives the same conclusion. Positivity alone does not resolve the problem.

The point is not that closure can never be discovered. It is that the memory/effect-space universe, or experiments that separate its effects, must be declared. An empirical finite-history test cannot independently establish that no longer omitted dependence exists. This obstruction is distinct from the rank-deficient iid-effect example: there the fixed regimes fail even with unlimited histories; here increasing the observation horizon eventually distinguishes the models.

Credit: this explicit shift-register stress test was supplied by the parallel scope audit. It is a standard finite-memory indistinguishability construction, not a novelty claim.
