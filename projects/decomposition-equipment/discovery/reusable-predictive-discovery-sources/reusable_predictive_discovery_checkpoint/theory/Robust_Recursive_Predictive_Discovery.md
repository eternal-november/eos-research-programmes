# Robust discovery of recursively executable predictive decompositions

Proof draft, 29 October 2026. This is a finite-horizon discovery theorem, not identification of physical components, an infinite-horizon guarantee, or a novelty claim. The positive local-response polytope and statistical confidence construction are established mechanisms. The new burden relative to the previous risk-specific milestone is their integration with unknown executable recursive summaries and a simultaneous, controller-independent prediction certificate.

## Plain-language abstract

A short message that answers one safety question need not describe a reusable subsystem. Here a proposed subsystem has actual memory, reads only permitted sensors and messages, and updates that memory at every step. Its predictive mechanisms must generate the *joint* next readings, not merely fit each sensor separately. One common implementation must work across all permitted control choices and all histories that the evidence leaves possible.

The construction searches the component groupings, memory updates and message programs. For each proposed program, a finite linear program finds—or rules out—a positive shared-source predictive implementation whose total error is small for every evidence-compatible environment and every controller in a declared family. The result does not recover a hidden whole-state model first. Nor does it declare the actual environment's hidden noise independent: independence is a property of the proposed simulator, whose predictions are checked against the unresolved environment family. Persistent hidden influences that its memory fails to capture appear as prediction error.

This is an exact, potentially expensive synthesis result for finite horizons and bounded implementation resources. An approximate predictor need not itself satisfy every evidence interval exactly; it approximates the compatible laws in the stated transcript metric. Its uncertainty set still requires valid experiments and confidence bounds. It cannot manufacture missing correlations, validate unmeasured physical hazards, or establish a compact infinite-horizon model from finite logs. The important gain over one-task compression is a common reusable prediction guarantee covering complete action/readout records and consequently every bounded task score on those records.

## 1. Evidence and controllers, without a supplied hidden architecture

Let O be a finite joint readout alphabet and A a finite action alphabet. A separate finite startup alphabet O_init is permitted (for example, an actually observed warmup record); initial sums below range over O_init, and subsequent readout sums range over O. Taking O_init=O is the simplest case. Startup access and warmup acquisition remain charged. Fix horizon H. A full record is

    omega = (o_0,a_0,o_1,...,a_(H-1),o_H).

Write h_t=(o_0,a_0,...,o_t). Prefix masses p(h_t), p(h_t,a), p(h_t,a,o) are linear sums of complete-record masses. A known exploration policy e_t(a|h_t) generated the data, with exogenous randomization and policy-invariant environment response. The finite causal-law polytope imposes

    p >= 0,  sum_omega p(omega)=1,
    p(h_t,a)=e_t(a|h_t) p(h_t).

Add only justified linear evidence constraints l <= Fp <= u (aligned observed patches, calibrated experimental statements, etc.). Denote the resulting nonempty polytope C. On the statistical confidence event, the true exploration law belongs to C. This is an assumption on the evidence procedure, not a theorem that every available data set satisfies it. Empty C is inconsistent evidence, not successful certification.

A declared control family Pi consists of behavioral policies on these histories. For the main effective finite LP use all policies choosing actions from a specified nonempty set A_t(h) at each history; this is a rectangular family of policy choices, NOT a rectangularization of environmental uncertainty. Require e_t(a|h)>0 for all admitted actions at all syntactically admitted histories. The main statement uses the full finite history tree, with total controller and predictor tables. A restricted prefix domain is valid only after proving both true and predictor processes remain in it, or explicitly totalizing their continuation outside it (for example with an accounted failure symbol). Zero true-law mass alone does not justify leaving the controller undefined on histories the predictor can reach. Uniform quantitative coverage is not required for exact algebra, but small exploration probabilities can make data requirements enormous.

For pi in Pi set

    w_pi(h_t,a) = product_(s=0)^t pi_s(a_s|h_s)/e_s(a_s|h_s),

where a_t=a. Products and denominators are policy quantities, not divisions by candidate p masses. At prefixes with a zero exploration denominator outside the permitted domain set w=0. Under the support condition, change of policy gives

    p^pi(h_t,a)=w_pi(h_t,a) p(h_t,a).

Every p in C induces a causal environment kernel on its positive prefixes; arbitrary choices on zero prefixes do not affect any admitted-policy law because exploration covers the family. Denote the resulting law by P_(p,pi). No finite latent-state, innovation independence, Markov order or physical component assumption is being imposed on p.

## 2. Unknown recursive executable decompositions

A resource signature names raw readout/action ports, local processors, sensor access, permitted communication phases and channels, finite memory bounds, and permitted shared-source access. These are actual implementation capabilities, not hidden mechanism equations.

A candidate D selects:

* a grouping/assignment of named readout ports to output components, subject to the declared ownership rules;
* local finite memory alphabets Z_i and initialization programs;
* local message encoders, routing and received-message decoders;
* recursively reused memory-update tables;
* local predictive input contexts c_i, built only from locally stored memory, permitted action ports and messages delivered before generation of the next output.

All of these tables and admissible wiring choices are unknown in synthesis. Bounds make the program family finite. The finite-state program is evaluated on an arbitrary raw prefix h, giving z_D(h); its local context is c_i^D(h,a). No processor may read the entire h unless that access is expressly permitted. Evaluation uses the typed scheduled-circuit semantics of references/safety_representation/Executable_Observer_Calculus.md. An update at one occurrence and the same update at another occurrence are the SAME table. Overlapping requested views retain actual common sensor/memory/source identifiers.

In a simulator, after generating o_(t+1), the SAME executable observer update reads the generated permitted ports and messages and computes z_D(h_t,a,o_(t+1)). Hence recursive update is not a table indexed by an inaccessible latent state. Initialization has its own read/communication/memory costs. An arbitrary mathematical quotient of histories is not admitted unless this program implements it.

A finite-horizon time counter may be included only if its memory is charged. This theorem does not hide an unbounded history inside a free clock or initialization oracle. Nor does a small declared memory alphabet establish a small search space.

## 3. Positive predictive implementation

For fixed D let S_D be the finite set of deterministic response strategies allowed by the implementation signature. In the simplest common-source model a strategy sigma consists of functions

    f_i^sigma : C_i -> O_i

for the owned output components. The same function is used at every context/time where its identifier occurs. A probability vector mu on S_D defines

    K_(D,mu)(o|h,a)
      = sum_sigma mu_sigma product_i 1[o_i=f_i^sigma(c_i^D(h,a))].       (1)

Thus K is linear in mu. One fresh draw sigma~mu per time step is shared by the components. It is independent of the current contexts in the predictor implementation; the deterministic responses can depend on their local contexts. The mixture is ONE vector for all contexts and occurrences, not a separate fitted coupling for each action or history. Source-sharing permissions may restrict S_D or require separate source structure. The linear-mixture theorem below applies whenever the admitted implementation kernels form a declared finite convex hull; independent-source factorizations can be nonconvex and are not silently covered.

Crucial interpretation: (1) restricts the proposed reusable simulator. It does NOT assume the real environment has fresh noise. A persistent actual hidden influence is allowed in every p in C. If D's recursively computed states do not retain enough of its observable history, the uniform residual test below will reject the predictor or charge its error. A successful approximate predictor does not identify the physical source law.

Let nu be the predictor's initial readout distribution, implemented by an admitted startup source protocol. For notational simplicity take arbitrary nu in Delta(O_init); restrictions to a finite convex hull of executable startup strategies remain linear. A fully distributed initial source is not free: source access and initialization storage must be charged. The generated law Q_(D,mu,nu,pi) samples o_0~nu, initializes D, runs the same controller pi on generated records, samples the joint next output with (1), and updates D recursively. This is a positive normalized law, with no negative probabilities or incompatible independently selected marginal sources.

An alternative continuation-only version starts predictor and true process from the same externally supplied initial readout law; then omit the initial residual, but claim only a conditional/continuation predictor, not a full generative startup guarantee.

## 4. Weighted joint prediction discrepancy

For p,pi define

    J_(p,pi)(D,mu,nu)
      = (1/2) sum_o |p(o_0=o)-nu(o)|
        + (1/2) sum_(t=0)^(H-1) sum_(h_t,a,o)
             w_pi(h_t,a)
             |p(h_t,a,o)-p(h_t,a) K_(D,mu)(o|h_t,a)|.               (2)

Define J(D,mu,nu)=sup_(p in C, pi in Pi) J_(p,pi).

The expression uses JOINT output o. Separate marginal residuals do not bound it: two output bits can have identical fair marginals under perfect agreement and perfect disagreement. No summing of local marginal errors repairs that missing dependence without an independently justified coupling argument.

Zero-mass prefixes have exactly zero residual. There is no conditional-probability division by zero. Unsupported interventions are excluded by the support contract, not assigned spurious certainty. The same p is retained throughout a candidate execution. We have not replaced C by independently chosen adversarial transition rows.

For positive p(h,a), write P_p(o|h,a)=p(h,a,o)/p(h,a). Equation (2) is precisely

    TV(p_0,nu) + sum_t E_(P_(p,pi))[
                       TV(P_p(.|h_t,a_t),K_(D,mu)(.|h_t,a_t))].    (3)

This is weighted by the TRUE prefix occupation law, not by the predictor's visitation law. That distinction is important when rare histories are being compressed.

## 5. Controller-uniform predictive transfer and approximate completeness

**Theorem 1.** For every fixed D,mu,nu, define

    Delta = sup_(p in C,pi in Pi)
                TV(P_(p,pi),Q_(D,mu,nu,pi)).

Then

    Delta <= min(1,J),                 J <= (2H+1) Delta.         (4)

In particular J=0 iff the predictor exactly reproduces every admitted controller's whole action/readout law for every p in C. If J<=epsilon, every [0,1]-valued function g of the complete record obeys

    |E_(P_(p,pi))g - E_(Q_(D,mu,nu,pi))g| <= min(1,epsilon)       (5)

simultaneously over p,pi and g. Thus the predictive decomposition transfers between tasks and controllers without refitting its local update/response mechanism. A controller outside Pi, a longer horizon, or a hazard not represented/soundly bounded by these readouts is not covered.

**Proof of the upper bound.** For fixed p,pi compare true and predictor prefixes. Their action kernels are the same pi at each raw history, so adjoining the next action does not increase prefix TV. Replacing the true output transition by K at a true prefix changes the joint prefix/output law by exactly the corresponding expected conditional TV in (3). Applying K to two different prefix laws is a stochastic map and does not increase TV. Triangle inequality consequently gives

    d_(t+1) <= d_t + E_true[TV(P_p(.|h_t,a_t),K(.|h_t,a_t))].

Initialize d_0=TV(p_0,nu), iterate, and take suprema. TV is at most 1. This argument includes adaptive feedback because the two processes use the same controller kernel on the common raw-history alphabet. It does not assume their actually sampled actions can be coupled independently of history.

**Proof of the reverse bound.** Fix p,pi, let P_t,Q_t be their prefix/action laws, and P_(t+1),Q_(t+1) the extended laws. Consider the intermediate law P_t K. Triangle inequality gives

    E_(P_t) TV(P_p(.|h,a),K(.|h,a))
      = TV(P_(t+1),P_t K)
      <= TV(P_(t+1),Q_(t+1)) + TV(Q_t K,P_t K)
      <= TV(P_(t+1),Q_(t+1)) + TV(Q_t,P_t)
      <= 2 TV(P_full,Q_full).

Marginalization gives TV(p_0,nu)<=TV(P_full,Q_full). Sum H terms and take suprema. This also proves exact equivalence, without an assumption that all summary states are visited. The factor 2H+1 is a general bound, not a claim of sharpness. QED.

**Interpretation.** J is a sufficient path-law error certificate that can be conservative by a horizon factor, not an arbitrary unrelated surrogate. If some implementation in the declared language has true worst-path error eta, the optimum J for that same implementation is at most (2H+1)eta. Exact bounded-horizon predictive realization is characterized without strengthening the goal to equality at unreachable histories.

## 6. Fixed-program synthesis is a finite linear program

Let V(C)={p^1,...,p^N} be the vertices of the nonempty bounded confidence polytope. Let Pi_det be the finite deterministic policies choosing actions in A_t(h). For fixed D use variables mu_sigma>=0 with sum mu=1; nu_o>=0 with sum nu=1; nonnegative r^v_0(o), r^v_t(h,a,o); and epsilon. Impose

    r^v_0(o) >= +(p^v_0(o)-nu_o),
    r^v_0(o) >= -(p^v_0(o)-nu_o),
    r^v_t(h,a,o) >= +(p^v(h,a,o)-p^v(h,a)K_(D,mu)(o|h,a)),
    r^v_t(h,a,o) >= -(p^v(h,a,o)-p^v(h,a)K_(D,mu)(o|h,a)),

and for every v and pi in Pi_det,

    (1/2) sum_o r^v_0(o)
      + (1/2) sum_(t,h,a,o) w_pi(h,a) r^v_t(h,a,o) <= epsilon.    (LP)

Everything is linear because the vertex probabilities and policy weights are constants and K is linear in mu. Executable startup-mixture variables can replace unrestricted nu.

**Theorem 2.** The LP optimum equals min_(mu,nu) J(D,mu,nu). In particular its feasible solutions at epsilon are exactly the positive shared-response predictors for D with J<=epsilon.

**Proof.** For fixed p,pi the discrepancy is convex in p since each residual is the absolute value of a linear function of p (K is fixed). A convex function on a finite polytope achieves a maximum at some vertex: if p=sum_v alpha_v p^v, J_(p,pi)<=sum_v alpha_v J_(p^v,pi)<=max_v J_(p^v,pi). Thus restricting the outer maximum to vertices is exact, although vertex enumeration may be huge.

For fixed p,K, the policy-dependent sum is an expected cumulative nonnegative cost on the finite history tree, with arbitrary history-dependent allowed actions. Its maximum over behavioral policies has a deterministic optimizer by backwards maximization. Equivalently it is affine in each separate history's policy probability vector while the others are held fixed; each local simplex can be replaced by a maximizing vertex. No policy restriction coupling choices across histories has been assumed. If such restrictions are desired, enumerate the actual finite controller family or supply a separate exact optimizer for that family; the rectangular-policy argument is then unavailable. In particular, a reused stationary randomized controller table need not have a deterministic optimizer, and its behavior set need not be a strategy polytope in those reused parameters. Enlarging a partially observed controller family to the full-history rectangular family is sound but may be conservative, rather than exact for the smaller family.

The r variables can be set to the actual absolute residuals. Conversely they dominate those residuals, and all weights are nonnegative, so every LP feasible assignment bounds the true J. This proves equality. QED.

For rational evidence and rational exploration probabilities the LP has rational data. Nonempty rational feasible sets have rational certificates. Exact arithmetic can verify them; floating-point feasibility tolerances require an explicitly outward-rounded error allowance. A certificate's existence is not a guarantee of short bit length relative to a compact unexpanded input description.

## 7. Discovery theorem: unknown boundaries, memories and interfaces

**Theorem 3.** Fix a finite implementable program budget B and a finite policy horizon H. Enumerate all well-typed observer programs D in B (including unknown grouping, memories, updates and messages). Solve the LP of Theorem 2 for each. Retain programs admitting J<=epsilon, and minimize the declared resource order among them. This procedure:

1. constructs a recursively executable positive predictive decomposition with the uniform guarantee (5), if one exists within B with certified discrepancy J<=epsilon;
2. retains alternative decompositions rather than identifying an arbitrary one as the physical architecture;
3. is complete within B for J<=epsilon, and therefore complete for exact predictive realization when epsilon=0;
4. if no program passes, proves failure only for this resource language, evidence set, controller family, horizon and error criterion;
5. has approximate completeness: any program in B with worst-path TV at most eta is accepted at threshold (2H+1)eta.

**Proof.** Finite syntax compilation checks executable causality and persistent table identity. Each program's realization optimization is exact by Theorem 2. Theorem 1 gives the claimed prediction guarantee. Enumeration covers all programs in B, so a witness cannot be missed. Resource minimization is finite. No step interprets an arbitrary true-law vertex as a supplied finite hidden mechanism. QED.

In Theorem 3, B bounds discrete program structure, memory carriers, wiring, and any explicitly enumerated source support. The plain LP does NOT impose an arbitrary hard bound on the bit length or denominators of source/startup probabilities. Rational feasible weights are obtained from the LP and their encoding length is reported and charged separately; it can be large. If a hard probability-encoding budget is part of the requested implementation contract, enumerate the finite allowed rational weight vectors (or add an exact discrete encoding restriction) before accepting a solution. The corresponding completeness claim is then for that restricted search, not for the unrestricted LP.

Shared-source cardinality/resource bounds must be part of B if they matter. A bound on the number of installed deterministic shared-response strategies can be handled by enumerating permitted supports then solving the corresponding LP. This is not the same as bounding the shared-source alphabet while allowing free private randomization: that latter restriction is generally a nonconvex mixture-of-products problem, as explained in Positive_Joint_Realization.md. It is not a linear sparsity penalty automatically solved by (LP). The accompanying positive-realization module gives a finite generic support bound but not a cheap implementation claim.

This is a discovery procedure, not a practical complexity theorem. It enumerates representations, not a catalogue of physical latent worlds. Nevertheless it can be exponentially worse than reconstructing a centralized predictor. History alphabets, confidence-polytope vertices, policy trees, response strategies and program counts can each explode. A sparse physical wiring graph by itself bounds none of these quantities. Compact factorization or oracle-based improvements need separate theorems with actual width and precision bounds.

## 8. Shared views, composition and uncertainty

One can request several overlapping predictive cuts by synthesizing one combined D whose local views share the same actual readout coordinates, persistent tables, messages and source registry. Their response equations use one global positive law K; duplicate output ports are equated, never independently sampled. Projection of the certified full record law yields predictions for every view and every joint combination of views. Thus compatibility is established by a constructed common implementation, rather than by multiplying independently fitted local predictions.

The guarantee does not require a unique mu. Distinct mu can induce the same K, or differ only at unreachable contexts; different D can be observationally equivalent for Pi,H. Preserve this fiber of solutions. The theorem does not resolve counterfactual interventions outside Pi, nor a physical source topology not determined by the recorded laws.

Coarsening or changing a boundary changes contexts and the response polytope; it must be rechecked. A valid marginal projection need not retain the messages or memory needed to regenerate the joint behavior. A proof of exact simulation by an executable adapter is sufficient to transport the predictor; merely matching marginal distributions is not.

The confidence set is shared across every program and controller. If it has simultaneous coverage 1-delta, arbitrary data-dependent selection among the programs preserves that event; no extra union bound over D is necessary because the statement is already universal over p in C. But constructing F or its confidence bounds after examining data requires its own valid simultaneous/held-out procedure. Representation search does not fix invalid statistical inference.

A poor certificate can have distinct causes: missing joint evidence, wide sampling uncertainty, insufficient memory, insufficient messages, or a forbidden shared-source implementation. These are not interchangeable. LP infeasibility supplies finite linear separating certificates relative to the declared constraints, and a violated solution gives histories/actions/laws witnessing residual. It need not produce one intuitive physical explanation, and coupled robust infeasibility may require several alternative laws rather than one universal bad law.

## 9. Nonclaims and meaningful next checks

* Finite logs without regularity do not justify exact future extrapolation past H. Repeated update tables are a reusable implementation design, not evidence for their correctness indefinitely.
* The model can preserve prediction while misdescribing latent physical mechanisms. This is predictive decomposition, not physical identification.
* Positive realization is implementation-relative. A shared random source distributed without a channel must be an allowed capability, not a free physical resource.
* Complete raw aligned records can permit a central predictor. Distributed decomposition earns its value only through actual access, memory, timing, communication or reuse requirements.
* Controller-family transfer is not controller synthesis and is not a physical safety certificate unless the hazard is observed or related to observations by a sound separate contract.
* Local rank, local one-step fits, local marginal prediction errors and local positivity do not establish the joint LP certificate.
* No connection to original graph-cut C5, full virtual-equipment reconstruction, or its unresolved cell-generation obligation is asserted here.

The decisive finite test should search an unknown recursive memory/interface program, demonstrate nontrivial reuse under more than one adaptive controller, retain at least one unresolved physical/source alternative, and exhibit a competing cheaper representation rejected by genuinely joint temporal evidence. A one-step Bell example alone is a supporting obstruction, not validation of the whole discovery theorem.

## 10. Retaining unresolved laws: a persistent predictive-family extension

The single-predictor quantifier above is deliberately strong:

    there exists one executable predictor Q such that every p in C is close to Q.

If C retains large genuine predictive ambiguity, no such Q should exist. A reusable representation of uncertainty can instead retain a *family* of common-code predictors. The following construction is exact as a family approximation; its extra recursive information cost must not be concealed.

Fix one executable observer program D. For every vertex p^v of C, synthesize a positive predictor Q_v with the SAME D and local context interfaces, but potentially different startup/source parameters (nu^v,mu^v). Require

    sup_(pi in Pi) J_(p^v,pi)(D,mu^v,nu^v) <= epsilon_v.           (6)

These are independent finite LPs once D is fixed. One can search D against all the LPs jointly. This has weaker epistemic quantifiers than Theorem 2: a single parameter vector is no longer required to fit all evidence worlds.

For alpha in Delta({1,...,N}) let p_alpha=sum_v alpha_v p^v. Define Q_alpha by drawing one branch V~alpha AT INITIALIZATION, retaining it for the WHOLE episode, then running Q_V under the installed controller. The branch is not redrawn per step or after a controller choice.

**Theorem 4 (coherent family approximation).** For every alpha and every pi in Pi,

    TV(P_(p_alpha,pi),Q_(alpha,pi)) <= sum_v alpha_v epsilon_v.   (7)

Every p in C has such an alpha. Conversely every alpha defines a p_alpha in C. Hence the confidence-law family and the persistent-mixture predictor family have policy-uniform Hausdorff distance at most max_v epsilon_v. This family guarantee preserves unresolved predictive alternatives instead of forcing them into one point predictor. The same alpha is used under every controller; the matching is not selected after seeing the controller.

**Proof.** Change of policy is the same linear trajectory reweighting for every p, so

    P_(p_alpha,pi)=sum_v alpha_v P_(p^v,pi).

A persistent initial branch gives Q_(alpha,pi)=sum_v alpha_v Q_(v,pi), even under feedback: the controller is the same measurable rule on the generated past in each branch. Convexity of total variation and Theorem 1 prove (7), simultaneously in pi. Every point in C is a convex combination of its vertices, and every such combination belongs to C. These two facts give both directions of the Hausdorff statement in the metric d(P,Q)=sup_pi TV(P^pi,Q^pi). This is a statement about observable causal law families, not uniquely identified latent branches. QED.

The persistent mixture is essential. For example, choose a coin bias theta in {1/4,3/4} once and then generate iid outcomes conditional on theta. Each fixed-bias model has probability 3/8 of two consecutive unequal outcomes. A transition-by-transition selector choosing bias 3/4 after a zero and 1/4 after a one gives probability 3/4 of unequal outcomes. It is not a mixture of the two original complete-process laws. Therefore replacing the family by a set of allowed next-step rows and allowing arbitrary row selection destroys this theorem.

### The cost of using the family to predict from actual readouts

The generative implementation of Q_alpha can retain its sampled branch V in a shared source register and run its components locally. That register is a hidden state of the SIMULATOR. It is not a branch label that an installed observer can read from the physical environment.

For predictive use on actual readouts, branch likelihoods have the recursive update

    L_v(o_0)=nu^v(o_0),
    L_v(h_t,a,o)=L_v(h_t) K_v(o|c_D(h_t,a)).                     (8)

For a specified prior alpha with positive denominator,

    beta_v(h)=alpha_v L_v(h) / sum_j alpha_j L_j(h),
    Q_alpha(o_next|h,a)=sum_v beta_v(h) K_v(o_next|c_D(h,a)).    (9)

Here beta is a conditional distribution inside the particular generative model Q_alpha. It is NOT a Bayesian posterior probability that physical world v is true, and does not add statistical confidence. If alpha is unresolved, retain the entire parameterized family beta(h;alpha) with the SAME initial alpha carried through the episode; choosing a new alpha independently after each history changes the family. The policy factors cancel because the same controller rule is used in every branch and does not directly observe V. On a zero-denominator history the model assigns zero probability; any continuation is definable, but encountering that history requires the declared out-of-model/error handling, not a confident posterior.

Equations (8)–(9) are an actual recursive update, but they need not be a finite-state local interface. They may require a continuously valued posterior, or an unbounded set of rational likelihood values over an unbounded horizon. Computing a joint likelihood can require gathering readouts that no individual component is permitted to see. Thus Theorem 4 alone does NOT make the original D a sufficient finite local predictor for the entire family.

For fixed H and rational vertex predictors, storing the unnormalized likelihood vector is an exact finite-length arithmetic implementation: if each probability numerator/denominator has at most b bits, a direct product representation has O(Hb) bits per branch (with an additional initial-factor bound), before overhead for addition, normalization and representation of alpha. A simpler bound follows by retaining the sequence of at most H+1 rational factors and evaluating when needed. This gives O(NHb) storage, not O(log N) alone. These costs are upper bounds for a declared rational implementation, not necessarily optimal. An arbitrary real alpha is not an exactly stored finite-bit probability vector. Unknown alpha can remain symbolic through the rational likelihood coefficients; evaluating an entire posterior family then requires optimization over alpha, not one known numerical state. A numerical exact implementation must separately specify rational alpha and charge its bit length, or use explicitly controlled approximation.

A sufficient execution contract for (8) is a permitted processor that receives the joint readout needed to evaluate every K_v, stores the likelihood vector, and communicates any requested posterior predictive summaries before their deadlines. Alternatively a separately proved distributed likelihood circuit can supply the same values. These are ADDITIONAL resources to be included in discovery, not free boundary operations. If the intended budget forbids them, the family approximation remains a law-level certificate and the reusable executable family-interface obligation is still open.

This limitation is productive: persistent uncertainty can be represented without resolving physical architecture, but its predictive cost may reside in cross-component likelihood computation and epistemic memory rather than in the originally discovered local state variables. A small collection of individually executable predictors does not imply a comparably small executable predictor for their persistent mixture.

## 11. Source-evidence dual certificates without enumerating confidence vertices

The vertex LP is a clean existence proof, but it is not necessary to construct the confidence-polytope vertices in order to verify a candidate. There is an equivalent LP directly in the original evidence rows. This gives an explicit evidence-to-prediction certificate, although its policy/sign index set is generally enormous.

Write C={p>=0:Ap=b, l<=Fp<=u}, with p indexed by complete records and A including causal equalities. For each deterministic admitted policy pi choose signs

    s_0(o) in {-1,+1},
    s_t(h,a,o) in {-1,+1}.

Let d_(pi,s,mu) be the complete-record coefficient vector of the following linear expression in p:

    d^T p = (1/2) sum_o s_0(o) p_0(o)
      + (1/2) sum_(t,h,a,o) w_pi(h,a)s_t(h,a,o)
           [p(h,a,o)-p(h,a)K_(D,mu)(o|h,a)].

The vector d is affine in mu (the first residual terms are fixed), because every prefix mass is a linear function of p and K is linear in mu. Let c_s(nu)=-(1/2)sum_o s_0(o)nu(o). Then exactly

    J(D,mu,nu)=max_(pi in Pi_det,s) [ c_s(nu)+max_(p in C)d^T p ].

For every pair (pi,s), introduce its own dual variables y_(pi,s) free and lambda_(pi,s),eta_(pi,s)>=0. Require

    A^T y + F^T(lambda-eta) >= d_(pi,s,mu),
    b^T y + u^T lambda - l^T eta + c_s(nu) <= epsilon.           (DUAL)

Together with the simplex constraints for mu,nu, these are a finite LP and are equivalent to J<=epsilon. Indeed, sign maximization represents each absolute value exactly, and ordinary finite LP strong duality applies to the nonempty bounded inner confidence-law optimization. The same variables mu,nu occur in every dual certificate; they cannot change with the policy, sign pattern or evidence law.

A verified collection of these certificates proves prediction for every compatible causal law directly from the experimental evidence and causal equations. It does not first identify one global hidden model. Its explicit size can still be exponential in the whole history tree and far larger than a central predictor. Compact certificate sharing, separation oracles and local factor elimination are legitimate future improvements only after their actual complexity is proved; (DUAL) itself supplies no such bound.

For a fixed candidate and a selected pi,s, an optimizing primal p exposes a specific allowed law and signed joint temporal discrepancy. Such witnesses can guide additional measurements or changes to the recursive interface. A counterexample law permitted by current evidence need not be the true physical law, and a positive dual coefficient on an absent hypothetical observation is not data. Adding a new joint measurement requires its own actual acquisition and valid evidence interval.

## 12. A weighted conditional-envelope certificate without confidence vertices

A useful special evidence format gives a shorter certificate than enumerating confidence vertices or all signed trajectory tests. It also avoids requiring the rarest history to have enough samples for the same accuracy as common histories.

Fix D,K,nu and let r_0 bound TV(p_0,nu) for every p in C. Suppose the evidence establishes deterministic numbers a_t(h,a) in [0,1] such that, for every p in C and every prefix with p(h,a)>0,

    TV(P_p(.|h,a),K(.|h,a)) <= a_t(h,a).                       (10)

For example, simultaneous full-history conditional probability confidence bands give a conditional-distribution set B_(h,a). One may compute a=max_(r in B)TV(r,K), or use the explicit bound min(1,TV(empirical_row,K)+confidence_radius). A zero-count row has the full simplex unless other evidence restricts it; setting a=1 is always sound. Conditional evidence from a short pooled window is NOT a valid full-history band without an additional memory/regularity promise.

The confidence event must cover all rows used in the certificate, including data-dependent program selection. Simultaneously valid distribution sets B_(h,a) do this automatically for every K, since the event is about the true row, not a selected predictor. Valid conditional concentration also needs independent episodes or another justified sampling argument; randomness of the row counts must be handled by the statistical procedure.

Define

    C_Q(a) = sup_(pi in Pi) E_(Q_pi)[sum_(t=0)^(H-1) a_t(h_t,a_t)].

**Corollary 5 (predictor-occupation certificate).** Under (10),

    Delta <= min(1, r_0 + C_Q(a)).                              (11)

For the rectangular full-history controller family, C_Q(a) is computed exactly by the finite backwards recursion

    V_H(h_H)=0,
    V_t(h)=max_(a in A_t(h)) [a_t(h,a)
                       + sum_o K(o|h,a) V_(t+1)(h,a,o)],
    C_Q(a)=sum_(o_0) nu(o_0)V_0(o_0).                         (12)

Thus low-confidence rows are charged by how often the proposed predictor can encounter them under the WORST admitted controller, not by their exploration frequency and not uniformly by the least row count. No confidence-polytope vertices or hidden whole-state reconstruction are required. The full history tree may still be exponentially large; (12) alone is not a polynomial complexity theorem.

**Proof.** For each p choose its environment kernel at every positive exploration prefix by conditionalization. At zero exploration prefixes, extend this kernel by K. Choose this extension once for p and K, independently of pi. Exploration coverage ensures a prefix with zero exploration probability also has zero probability under every admitted true controller, so this extension changes none of the true laws P_(p,pi). It makes the conditional discrepancy zero at the remaining prefixes; consequently (10) bounds it on the ENTIRE history tree.

Let d_t be the TV distance between true and predictor prefixes through o_t, for fixed p,pi. Adjoining their common controller action kernel cannot increase TV. Use the TRUE extended output kernel as a stochastic map on both prefix/action laws. Its application to these two laws changes TV by at most d_t. Changing the output kernel on the PREDICTOR prefix law costs at most E_(Q_pi)a_t. Therefore

    d_(t+1) <= d_t + E_(Q_pi)a_t(h_t,a_t).

Start with d_0<=r_0, sum and maximize over pi. This is the reverse-prefix version of the hybrid argument; it does not replace the true conditional-law family by independently selected rows. Dynamic programming on the candidate predictor proves (12). QED.

There is also an explicit bound for the original J certificate. Let

    M_t = max_(h,a) a_t(h,a) - min_(h,a) a_t(h,a),
    b_s = 1 + sum_(t>s) M_t.

Then

    J <= r_0(1+sum_t M_t)
           + sup_(pi in Pi) E_(Q_pi)[sum_s b_s a_s(h_s,a_s)].    (13)

The final supremum is another instance of (12), with stage costs b_s a_s. In particular one does not need to maximize each stage separately, potentially using inconsistent worst policies.

**Proof of (13).** For fixed p,pi, bounded-function TV duality gives

    E_(P_pi)a_t <= E_(Q_pi)a_t + M_t d_t.

The action kernel is common, so the prefix/action distance is at most d_t. The preceding hybrid proof gives d_t<=r_0+sum_(s<t)E_(Q_pi)a_s. Equation (3) and (10) therefore yield

    J_(p,pi) <= r_0 + sum_t [E_Q a_t
                           + M_t(r_0+sum_(s<t)E_Q a_s)]
               = r_0(1+sum_t M_t) + sum_s b_s E_Q a_s.

Take suprema. Replacing M_t by max a_t is also safe but weaker. Prefix distances can additionally be capped at 1 when useful; (13) is the simpler linear-cost form. QED.

This corollary certifies a proposed predictor rather than making global synthesis convex in K: the occupation law in (12) depends nonlinearly on its transition parameters. Exact finite program search can use it as an additional sound acceptance certificate. Its principal advantage is weighted verification and a transparent worst-controller witness. It does not turn missing joint observations into narrow conditional bands or grant an arbitrary controller permission to access new readouts.
