# Discovery of recursive environmental components from observable records

Proof synthesis, 29 October 2026. The constructive main class below is deliberately narrower than arbitrary controlled hidden-state systems. Neither the class promise nor independence of fresh innovations is claimed to be certified against all possible environments by finite records.

## Plain abstract

We give a constructive route from action/readout records to reusable environmental semantics without first learning a whole-system state. The route discovers bounded local predictive scopes, minimizes recursively executable observable memory, and discovers unknown independent groups of shared stochastic innovations, including groups invisible to pairwise dependence tests. A single positive joint source realization supports all later feedback controllers while their local contexts remain in evidence coverage. Alternative compressed memories and crossing ownership descriptions are retained rather than identified with a unique physical architecture. Communication restrictions and source budgets are checked on a common response construction; independent successful local fits are not substituted for that construction. The general theorem is conditional on an unknown bounded-block, sparse finite-observable-memory conditional law; an additive-innovation subclass admits a more efficient explicit discovery algorithm. Arbitrary hidden-state recovery remains open.

## 1. Observable contract and structural class

There are n labeled readout/action ports. Each action coordinate lies in a finite alphabet A, each readout is an integer in [-M,M]. Time is discrete. Let X_t be the observable suffix of the last L action/readout pairs together with current action a_t. For S subset [n], X_t[S] is its restriction to ports S. This is a syntactic history dictionary, not a supplied sufficient state.

The structural universe is stationary (or has an explicitly recorded finite clock included and charged in X). It consists of laws for which there EXIST unknown sets T_i, |T_i|<=w, integer response functions f_i, and a fixed innovation law nu such that

    Y_{t,i} = f_i(X_t[T_i]) + E_{t,i}.                       (1)

The vectors E_t are iid with law nu, independent of the complete pre-output history and current intervention. All dependence of future outputs on older records must pass through the indicated finite suffixes. The class promise is pointwise on the declared continuation domain, not merely an equality under one logging policy. Initialization supplies an observed length-L suffix, or a separately accounted warmup law. A fixed initialization suffix is the cleanest theorem instance.

The finest partition of nu into mutually independent coordinate blocks exists, is unknown, and its blocks have size at most b. Existence and uniqueness are proved below. No parent set, memory quotient, block membership, conditional independence list, or separating probe is supplied. The numeric ceilings L,w,b and observable alphabets are supplied. Exact response identification uses the integer spacing in (1); without a known spacing/margin, only approximate predictions, not exact memory equivalence, follow.

The additive iid innovation assumption is substantive. In particular this does NOT learn arbitrary persistent latent noise, multiplicative/context-dependent innovation, arbitrary nonunifilar hidden state, or physical component ownership.

## 2. Acquisition and a coverage gate

Stage I contains N_1 independent endpoint records (X,Y), each from a reset/warmup/exploration episode. Their joint logging law is fixed; current actions are assigned without confounding. Dependence inside an episode is allowed. Conditional concentration uses independent endpoint records, not an iid assumption about consecutive timestamps.

For every S with |S|<=2w and every local context c, record its count N_S(c) and the conditional empirical mean mhat_{i,S}(c). Let J be the number of potential (i,S,c) rows. For a threshold m and radius e, with probability at least

    1 - 2 J exp(-m e^2/(2 M^2)),                            (2)

all rows with N_S(c)>=m satisfy |mhat_{i,S}(c)-m_{i,S}(c)|<=e. This holds for data-dependent row selection because the event covers all rows. Conditional on membership/count, each row consists of iid bounded observations; conditional Hoeffding and a union bound prove (2).

Define the evidence-covered full contexts C to be those x for which every restriction x[S], |S|<=2w, has N_S(x[S])>=m. The gate is executable from local count tables; it does not require enumerating full contexts. A controller can be stopped at first failure of this gate. Absence of failures in logging does not itself prove coverage for a new controller.

If a target family of full contexts has all its union-scope cylinders of logging probability at least rho, then N_1>=max(2m/rho,8 log(J/delta_c)/rho) makes their count coverage hold with probability at least 1-delta_c, by a binomial lower-tail bound. This can be expensive: rho is for complete union cylinders, not individual ports. It is not silently replaced by an action probability alone.

## 3. Unknown-scope discovery lemma

For every candidate U, |U|<=w, accept it for output i iff for every V, |V|<=w, and every empirical row on U union V with count at least m,

    |mhat_{i,U union V}(c) - mhat_{i,U}(c[U])| <= 2e.       (3)

True U=T_i passes on the event (2): both population means equal the same f_i(c[T_i])+E E_i. A passing U need not be uniquely minimal.

Choose one reference full context x0 in C; if none is available, abstain. For each passing U define

    fhat_i^U(u) = round(mhat_{i,U}(u)-mhat_{i,U}(x0[U])).     (4)

Use a declared arbitrary integer/sentinel value for unestimated local rows. If e<1/12, then on event (2), for every x in C,

    fhat_i^U(x[U]) = f_i(x[T_i])-f_i(x0[T_i]).              (5)

Proof: set V=T_i in (3). The conditional mean on U union T_i is f_i(x[T_i])+E E_i, because E_i is independent of all pre-output data. Its empirical estimate is within e, hence the empirical U mean is within 3e of that quantity. Apply the same argument at x0. Their difference is within 6e<1/2 of the integer on the right of (5), so rounding is exact. This proof does not assume every observed row is covered, nor that candidate U is correct outside C. It is valid simultaneously for all accepted scopes. QED.

Thus all accepted scopes recover the SAME response on coverage, in a common observable gauge, without identifying the physical parent set. The test search uses union widths 2w, not global history width nL. Checking only U rows, pairwise regressions, or individually supported inputs would not prove this lemma.

## 4. Recursive memory discovery (stable congruence, not row merging)

For a selected U, construct the finite suffix shift machine on its length-L local history words. Its input is the delivered current action/readout tuple; its next state drops the oldest tuple and appends the new one. Its Moore output label is the entire response vector a[U] -> fhat_i^U(history,a[U]), including sentinels for missing rows. Begin by grouping equal output-label vectors. Repeatedly split a block whenever two histories have successor states in different blocks for any delivered local symbol. This terminates in at most the number of local suffix states minus one strict refinement steps.

The final relation is the largest equivalence preserving labels and closed under every shift update. Induction on input-word length proves equivalent states yield identical response labels after every future word. Conversely, any label-preserving shift congruence is contained in every refinement partition by induction on iterations, hence in the final one. The quotient is therefore recursively executable and is the minimal deterministic Moore realization of this local table on its full chosen input language, up to isomorphism. Every removed distinction has been checked under all recursively generated continuations of the learned totalized table, not merely one-step output agreement. This is a finite model-side proof, not additional empirical coverage of those continuations.

The machine is an online observer of delivered records, not a hidden physical state claim. A product of its states across i is never enumerated. Its initialization is obtained by evaluating the observed initial suffix. Any local component must actually receive its required initialized state or observed suffix through a named, charged initialization provider. If a narrower partial language is desired, that language must itself be represented and proved closed; arbitrary off-coverage row choices can make this quotient larger than the smallest coverage-relative quotient.

## 5. Shared-innovation discovery without pair faithfulness

Use fresh Stage-II endpoint records whose full contexts pass the Stage-I gate. Selection must depend only on pre-output X, not on Y; rejection sampling then leaves innovations iid. For any chosen accepted scopes, set R_i=Y_i-fhat_i(X[U_i]). By (5), R=E+constant, so these residual vectors have one fixed law P, with exactly the same independent-block partition as nu. The same Stage-I gauge is used for every candidate.

Let K bound each residual alphabet (K=6M+1 is safe under the stated range). For every S with 1<=|S|<=b estimate Phat_S from N_2 residual vectors. With probability at least 1-delta_r, all these estimates have TV error at most r provided

    sum_{s=1}^b binom(n,s) (2^(K^s)-2) exp(-2 N_2 r^2)
        <= delta_r.                                      (6)

This follows by union-bounding Hoeffding over all nonempty proper events of each finite marginal. The logarithm of the enormous event count is O(K^b+b log n); the observation/table cost is still polynomial in n for fixed b and exponential in b. More efficient multinomial inequalities may replace (6).

For |S|>=2 define its split score

    Delta(S)=min_{empty!=A proper subset S}
        TV(P_S, P_A tensor P_{S\A}).                       (7)

The empirical score replaces each law by its empirical marginal. On the event (6), its error is at most 3r: one r for the joint row, two r for the two product marginals, using TV(p tensor q,p' tensor q')<=TV(p,p')+TV(q,q').

Create a hyperedge S whenever Deltahat(S)>3r. No such edge crosses an actual independent block boundary: any crossing S factors across the induced cut, giving Delta(S)=0. Suppose every true nonsingleton finest block B has Delta(B)>=gamma with gamma>6r. Then B itself is selected. Consequently the connected components of the selected hypergraph, including isolated vertices, recover the unknown finest block partition exactly. This detects pure q-way parity blocks: no pair-dependence premise is used.

The proof of unique finest partition is elementary. If P factors over a partition pi and over a cut A|A^c, marginalizing the latter factorization to B in pi shows P_B=P_{B intersect A} tensor P_{B\A}. Therefore P factors over the common refinement. Iterating over two partitions proves that all independent partitions have an independent common refinement. Finitely many partitions give a unique finest one; each of its nonsingleton blocks is irreducible under every split.

## 6. Positive joint realization, feedback reuse, crossing ambiguity

The constructive realization samples each learned block residual ONCE per tick, tags it by (tick,block), and supplies its coordinate projections to every consumer. Independently resampling overlapping projections is forbidden. Each output is its learned recursive response plus its projected residual. The same persistent learned tables and one block-law tuple are used throughout an episode. A full source value is always a finite positive witness; reduced source/communication budgets require a separate common-response feasibility test, not inference from local marginals.

Two alternative accepted scopes can be synchronized by a product of their local Moore observers, with union interfaces explicitly charged. Crossing output ownership partitions can use common intersections and shared original residual-event IDs. This is an operational common refinement, not automatically an original ordered C5 refinement. Fixed source encodings are not physical invariants: allowed local recodings must be synthesized before declaring a common-source obstruction.

On the high-probability events and with exact block recovery, the empirical product innovation law differs from the true law by at most sum_B TV(Phat_B,P_B)<=number_of_blocks*r. Each covered step therefore has this TV error, independently of how current actions were selected from earlier readouts. Coupling proves full stopped-transcript error <=H*number_of_blocks*r for EVERY causal feedback controller simultaneously, including controllers assembled or selected after discovery. No policy union bound is used. Full unstopped error additionally pays an explicitly bounded coverage-exit probability. This is conditional structural extrapolation, not model-free coverage of unseen policies.

Without a split margin one must retain coherent alternative partitions/laws rather than assert independence of the hypergraph components. The crossing stability lemma in Section 10 and the exact shared-response feasibility theorem in Section 13 apply here. Their proofs are independent of the additive specialization.

## 7. Cost and scope audit for the additive specialization

Mean-row count is at most n sum_{s<=2w}binom(n,s)|A|^s(|A|(2M+1))^(Ls). Scope tests enumerate only such local rows. Memory quotient search costs a polynomial in each explicit local suffix table, not the product of all component states. Residual marginal discovery costs O(N_2 sum_{s<=b}binom(n,s)) plus O(sum_{s<=b}binom(n,s)2^s K^s) split testing. General minimum-source/communication synthesis can be NP-hard; the canonical full block sampler avoids that optimization, with source support at most K^b per block. Data acquisition includes warmup/reset/selection costs; accepted endpoint count is not total raw episode count.

What this specialization establishes: constructive unknown scopes; exact response identification under spacing; discovered recursive memory; unknown higher-order innovation groups; one positive source witness; all covered feedback reuse. What is not established: model-free finite-memory certification, unique physical architecture, universal efficient hidden-state learning, or cost-free common refinement under arbitrary local permissions.

# Part II. A more general conditional-product discovery theorem

The additive theorem is an efficiently checkable special case, not the final generality of the finite-data result. The following construction learns conditional blocks directly and supports genuinely context-dependent stochastic kernels. It pays for a combinatorial synthesis stage, rather than claiming efficient arbitrary unknown-partition recovery.

## 8. Structural universe and local statistical event

Let the readout alphabet at each port have size k; integer outputs are no longer required. There EXIST an unknown partition pi* of [n], blocks of size at most b, unknown port scopes T_B of size at most w, and normalized kernels p_B such that, for every admitted pre-output history and intervention,

    P(Y=y | h,a) = product_{B in pi*} p_B(y_B | X[T_B]).     (8)

The X dictionary and observed initialization are as before. The kernels are stationary unless a finite clock is included explicitly. For the main statement the continuation domain is all syntactically admissible suffix/action contexts of the declared controlled kernel; for a narrower domain, the gate must also enforce its membership, or deployment must separately guarantee and charge domain exit. Counts of local cylinders alone do not prove global admissibility. This is an unknown conditional-product model class: its factorization is a hypothesis about the world, not something finite data can establish against unrestricted alternatives. Dependencies between blocks through past readouts or current actions are allowed. The conditional output kernel factors across the unknown blocks; all within-block coupling is retained. Fresh independent block sources are a positive simulator realization of this kernel, not an identification of the physical noise mechanism. Put d=bw.

For every nonempty output set S with |S|<=b and input scope W with |W|<=2d, estimate the conditional distribution phat_{S,W}(.|c). On independent endpoint records, with probability at least 1-delta, every row with count at least m has TV error at most eta if

    J_out (2^(k^b)-2) exp(-2m eta^2) <= delta,              (9)

where J_out is an upper bound on the number of (S,W,c) rows. One may replace k^b by k^|S| separately. Conditional on row membership/count, the observations are iid; TV equals the maximum discrepancy over output events, proving (9). The gate now requires all relevant input-cylinder counts of width at most 2d to be at least m. The gate can be evaluated without constructing its full domain, but its raw-suffix storage, lookups, information access and stopping signal MUST be charged separately from the learned predictive observer.

Every true marginal P_S(.|x) depends on at most d input ports: take the union T_S of T_B over true blocks meeting S. There are at most |S| such blocks. This elementary bound is why local tests can be complete within (8). Outside this structural universe, high-order hidden dependence defeats the conclusion.

## 9. A local catalogue and exact-cover synthesis, not enumeration of programs

For each possible output block C, 1<=|C|<=b, and scope U, |U|<=w, construct the positive empirical table

    q_{C,U}(.|u) = phat_{C,U}(.|u)

on sufficiently sampled rows; fill other rows by a declared fixed normalized distribution and mark them uncovered. This yields a catalogue of at most

    D_cat = [sum_{c=1}^b binom(n,c)] [sum_{u=0}^w binom(n,u)]

block/scope options, each represented by a local conditional table. Candidate models select disjoint catalogue blocks covering [n], together with their indicated scopes. They are positive normalized recursive laws by construction. In particular no bounded-program interpreter is enumerated.

For a candidate partition pi and selected scope U_C, let U_S be the union of U_C over candidate blocks meeting S. It has size at most d. Its candidate output marginal is

    Q_S(y_S|x[U_S])
       = product_{C in pi:C meets S}
           sum_{y_{C\S}} q_{C,U_C}(y_C|x[U_C]).             (10)

Accept a candidate iff, for every |S|<=b, every V with |V|<=d, and every sufficiently sampled context c on W=U_S union V,

    TV(phat_{S,W}(.|c), Q_S(.|c[U_S])) <= t.               (11)

Missing W rows are not tested and must fail the runtime coverage gate. A local block table row used by a tested W row has at least as many observations as that W row.

This selection problem has a finite local-constraint encoding. Give each output i a variable Z_i choosing a catalogue option containing i. Pairwise consistency constraints require that if option C is selected by one of its ports, every port in C selects that same option. This is exactly a partition into selected blocks. For each S, condition (11) is a factor depending only on (Z_i:i in S): these choices determine every selected block meeting S, its scopes, and (10). All V and local rows are evaluated inside that factor. No environmental global state appears in the constraint graph.

A minimum declared resource-cost satisfying assignment can be obtained by finite constraint elimination and backtracking. If the simplified explicit constraint graph has induced width kappa, variable-domain bound D, and factor evaluation cost T, standard variable elimination costs O(poly(n,factor_count) D^(kappa+1) T), plus the explicit factor tables/backpointers. This is an honest conditional algorithmic bound. Small b,w do NOT imply small kappa; unknown partition synthesis can remain NP-hard. Dropping identically true factors and filtering impossible local options are sound simplifications. An elimination order or a proof of its width is a computational certificate, not a supplied environmental partition.

### Completeness at a quantitative tolerance

On event (9), choose the actual blocks and actual scopes from the catalogue. Every learned block row differs from the true row by at most eta whenever that row is used by a tested context. Its S marginal differs from the true P_S by at most b eta, using product TV subadditivity. Since the empirical conditional law in (11) is within eta of P_S when W contains the actual U_S, the actual-block catalogue candidate passes at

    t=(b+1)eta.                                            (12)

Thus the unconstrained block/scope catalogue has a passing candidate on the confidence event. Additional communication/source/memory permissions may rule all candidates out; the correct result then is abstention under that execution contract, not a weakened implementation claim.

### Simultaneous small-memory synthesis without a physical probability grid

The statistical implication of (11) holds for ANY positive bounded-block/scope candidate, not just the empirical catalogue tables. Therefore the catalogue can be expanded into local unknown memory and kernel tables. For each proposed (C,U), use finite variables for

    alpha_C: local length-L suffixes -> {1,...,m_C},
    delta_C: {1,...,m_C} x delivered local record symbols -> {1,...,m_C},
    F_C: {1,...,m_C} x delivered current-action contexts -> probability simplex,

and impose every local shift equation (18), normalization/nonnegativity, and

    q_C(.|s,a) = F_C(.|alpha_C(s),a).                       (9a)

These equations force recursive closure; a collection of one-step row clusters is not accepted as memory. Scopes, state IDs, update entries, and response tables remain unknown and are selected by the constraints. The local suffix alphabet, memory ceiling, and communication permissions are budgets, not a supplied sufficient state. The construction never introduces a whole-system product-state table.

For a genuinely finite solver, probabilities may be chosen on an IMPLEMENTATION mesh with denominator D. This is not an assumption that physical probabilities lie on that mesh. Any d_y-outcome probability row has a normalized denominator-D approximation with TV at most d_y/D: round down all but one coordinate and assign the residual to the last. Choose a deterministic rounding rule so equal rows receive equal approximations. If the actual local suffix response machine has m_C states, rounding its state-response rows preserves its recursive update machine and uses at most m_C states.

Writing xi=k^b/D, the true blocks/scopes with these rounded observer rows have each block error at most xi. On event (9), this constructive candidate passes (11) at t=eta+b xi; alternatively, rounding estimated true-scope rows gives the more conservative t=(b+1)eta+b xi. The former existence statement uses the unknown true machine only to prove completeness of the finite synthesis search, not as input to the algorithm. Its variables range over all permitted local alpha, delta and mesh-valued F tables, constrained by the observable rows. A returned candidate is sound by Theorem 11 regardless of how it was found.

Consequently, if there exists a small recursive local realization within the offered scope/interface/memory budgets and a feasible shared-source protocol, sufficiently fine finite precision and a slackened observational tolerance allow discovery of a feasible candidate whose cost is no greater than that constructed finite-precision witness under the declared optimization objective. This does not promise cost no greater than an arbitrary exact-real realization: probability bit lengths, sampler latency and representation precision may increase even when state count is preserved. Restricted source/communication completeness requires that the approximation itself have a permitted positive witness; independent rounding of joint kernel rows need not preserve a restricted local-response polytope. A safe version quantizes an existing permitted source witness, or states completeness relative to candidates with such a witness. No unrestricted realizability premise is smuggled into that clause.

The finite-constraint width bound above applies to this enlarged synthesis graph only after charging these additional variables and their domains. General real-valued kernel variables instead give a semialgebraic feasibility problem (products appear in (10)); rational outward confidence thresholds permit standard exact real-algebraic decision procedures, but no efficient general bound is claimed. A finite mesh yields literal finite search and rational sampler probabilities, at the explicit approximation cost xi.

## 10. Crossing product stability: retaining ambiguity without rectangularizing it

**Lemma.** Let P and Q be distributions on n coordinates, with P product over partition tau and Q product over partition pi. Suppose every block of both partitions has size at most b and

    max_{1<=|S|<=b} TV(P_S,Q_S) <= zeta.

Then

    TV(P,Q) <= (|pi|+|tau|+|pi meet tau|) zeta <= 3n zeta.  (13)

Here pi meet tau is the partition into nonempty intersections. It is not assumed that P or Q factors over this common refinement.

**Proof.** Define R=product_{C in pi} P_C. Since P factors over tau, marginalization gives P_C=product_{B in tau}P_{B intersect C}, so also R=product_{B in tau,C in pi}P_{B intersect C}. Product coupling gives

    TV(Q,R) <= sum_{C in pi} TV(Q_C,P_C) <= |pi|zeta.

For each B in tau, Q_B=product_{C in pi}Q_{B intersect C}. Therefore

    TV(P_B,R_B)
      <= TV(P_B,Q_B)
          + TV(product_C Q_{B intersect C},product_C P_{B intersect C})
      <= [1 + number of nonempty B intersect C] zeta.

Both P and R factor over tau. Summing this inequality over B gives TV(P,R)<=(|tau|+|pi meet tau|)zeta. The triangle inequality proves (13). Every marginal used has at most b coordinates. QED.

This lemma is a stability statement about TWO coherent whole laws; it never forms independently chosen confidence rows. At zeta=0 it proves identifiability of the full law within the union of bounded-block product models from its b-coordinate marginals, although the physical partition and resource witnesses need not be unique. The proof constructs a positive comparison law R, not a common exact source realization of P and Q when they differ.

## 11. Main finite-data discovery and reuse theorem

**Theorem.** Under (8), independent endpoint acquisition, an observed common initialization suffix, and event (9), every model satisfying (11), including a data-selected minimum-cost one, obeys on every evidence-covered full context x

    TV(P(.|x),Q(.|x))
      <= epsilon := min(1,3n(t+eta)).                      (14)

For tolerance (12), epsilon<=min(1,3n(b+2)eta), and a passing unconstrained candidate exists. All accepted models retain one persistent selected partition, one tuple of normalized tables, and one recursive observer implementation throughout each rollout.

**Proof.** Fix S. The actual marginal P_S depends on its unknown T_S of size at most d. In (11) choose V=T_S. At a covered x, the row on U_S union T_S is available. Its population conditional law equals P_S(.|x), by the pointwise model promise (8). Hence (9) and (11) give TV(P_S(.|x),Q_S(.|x))<=t+eta. This holds for all |S|<=b. At the fixed x both P and Q factor over their respective block partitions; applying (13) proves (14). The event concerns only observable conditional rows and is simultaneous for all candidate choices, so no candidate-program union bound is needed. QED.

The confidence set can retain every passing model instead of selecting one. Every such model satisfies the same bound to the actual law, and two accepted models are within 2epsilon on each covered step by the triangle inequality. They are not asserted to admit exactly identical outputs under a common seed unless an additional exact common-realization check succeeds. Runtime must choose one coherent model or a declared episode-start mixture; changing unknown parameters independently at histories is a larger uncertainty model and is not the same conclusion.

### Stopped feedback transfer, with the exact coverage price

Let a causal controller be any stochastic kernel mapping observed past records to the next action; it may have arbitrary memory and may be constructed after seeing the discovery data. Before output at time t, evaluate the common coverage gate on the current observable suffix and chosen action. At first failure emit a distinguished cemetery symbol and stop. With H attempted steps, the stopped transcript laws satisfy

    TV(P_pi^stop,Q_pi^stop) <= min(1,H epsilon).             (15)

**Proof.** Couple controller randomness whenever histories agree. Before the first difference, both controllers therefore choose the same action and see the same gate result. On a covered step, maximal coupling of the two joint output kernels fails with probability at most epsilon; on an uncovered step both stopped processes emit the same cemetery symbol. A union bound on the H coupling opportunities proves (15). The same pointwise inequality works for every controller on the one data event; there is no union bound over controllers or action words. This is precisely why compositionally generated feedback policies are included, subject to their observable-access contract.

For the unstopped, totalized laws, let beta_Q(pi)=Q_pi(the gate fails within H). Couple until either an output mismatch occurs or the common gate fails. The probability of an output mismatch while still covered is at most H epsilon. The event of reaching a common gate failure before any mismatch is a subset of the Q marginal gate-failure event. Therefore

    TV(P_pi,Q_pi) <= min(1,H epsilon+beta_Q(pi)).            (16)

This is not the triangle bound with two exit probabilities. A certified upper bound on beta_Q may be computed from the selected model/controller, estimated with separate simulation confidence, or made zero by an enforceable coverage contract. The confidence/accounting of that calculation is additional. The stopped-law guarantee (15) remains valid without a beta bound. The raw-suffix coverage monitor is not automatically implemented by the minimized predictive observer. It may store a full n-port observed suffix (linear in nL symbols, not an exponential product-state table); its storage and communication are additional. Under an established all-target-context coverage contract, the runtime gate can be omitted on those target executions.

Any [0,1]-valued transcript score changes in expectation by at most the corresponding TV bound. Composing local controllers, switching among them based on readouts, or designing a new controller after discovery is allowed if the resulting controller uses only the permitted records and satisfies the stated coverage condition. This is stronger than a certificate for four frozen experimental controllers, but rests on the explicit structural universe (8), which that model-free certificate did not assume.

## 12. Discovering exact recursive memory when finite records permit it

For every selected block table q_C, build its local length-L suffix shift machine. Label a suffix by the entire current-action response table a[U_C] -> q_C(.|suffix,a[U_C]). Stable partition refinement as in Section 4 yields a minimal deterministic observer realizing this LEARNED stochastic response table. The state is not a stochastic hidden state: it is a recursively updated equivalence class of observable local histories. Its output sampler is positive and separate from its memory update.

Approximate empirical tables can prevent useful exact merges. This is not a proof defect to hide: without a margin or a permitted approximation loss, finite data cannot decide whether arbitrarily close rows are equal. Two legitimate options are (i) retain the larger stable observer, or (ii) synthesize a smaller observer/table and subject its resulting kernel to the same certificate (11). The latter can use finite table constraints but its search cost must be charged.

An explicit noncircular exact-recovery regime is available. Assume every true block probability is an integer multiple of 1/D, where D is known. Round each sufficiently sampled candidate block row to that grid; discard a candidate option if a rounded row is not normalized, and totalize uncovered rows by a grid-valued distribution. If eta<1/(2D), the actual-block candidate is rounded exactly on every used row. It passes (11) at t=eta. Every actual and candidate S marginal has entries with denominator dividing D^b. Thus, if

    2eta < D^(-b),                                         (17)

a passing candidate has exactly the same S marginal as the physical law on every covered context: a distinct pair of grid distributions has TV at least D^(-b), contradicting the bound 2eta. By (13) their entire joint kernels are equal there. Stable refinement then learns exact local predictive equivalence of the learned totalized table. If the covered local input language is complete and closed, it is also the exact minimal observable memory for that language. On partial coverage, no minimality claim beyond the learned totalization follows.

Condition (17) can be very expensive and is not part of the approximate theorem. It states precisely what quantized finite-precision assumption buys exact equivalence. The additive integer-response theorem instead obtains exact deterministic memory from response spacing while retaining continuously valued innovation probabilities.

## 13. Executable interfaces and a common positive response synthesis

The existence of a normalized kernel is not the existence of an implementation under restricted information flow. We now give the separate synthesis/checking stage. It is finite, constructive, and explicitly local in the selected block supports; the underlying local-response polytope is classical.

Fix a selected learned model Q, not a different fitted law for each requested decomposition. The protocol language in this section uses independent source events for its selected stochastic blocks; the feasibility theorem is exact within that language, not a proof of globally optimal source allocation across blocks. A request specifies output ownership charts, allowed delivered pre-output views, permitted post-output observation streams, clocks, allowed message providers, and source budgets. No component may inspect the central observer state for free. A proposed view/encoder must be executable by its named provider from that provider's declared inputs at that stage. Raw scope projections are a constructive default; smaller nonlinear encoders can be included as finite local table variables.

### Recursive interface check

A proposed local observer map alpha from an explicit local suffix machine into a finite state set must satisfy, on every certified local transition,

    alpha(shift(s,z)) = U(alpha(s), delivered_post_symbol(s,z)).   (18)

Its current output context must be computable from alpha(s) and the delivered pre-output symbol. These are concrete finite equations over the union of their local supports. They are not tested only on realized sample transitions. Full-table checking is relative to the learned finite machine; physical correctness is separately supplied by (14) and the gate.

For raw stream projection interfaces, coarsest observers are computed by stable refinement. For arbitrary finite encoders, alpha, U and encoder tables can instead be unknowns in these finite equations; a satisfying assignment supplies their actual executable tables. A failed equation must split memory, enlarge a permitted message, or reject the proposal. The compiler never assumes that a label-preserving one-step state merge is recursive.

### One source block and several crossing charts

For a selected stochastic block B, let Z_B be the finite contexts needed to evaluate its learned kernel K_B(y_B|z). Enumerate them only on the union of B's actual local supports and proposed view supports, not on the whole environmental state. A conservative constructive choice is every syntactically possible local context on that union. Restricting to those with a globally covered extension is an additional constraint-projection problem whose cost must be charged; it is not presumed free. In chart d, each owner j of a part of B receives an allowed view v_{d,j}(z), with context alphabet C_{d,j}, and must emit y_{B intersect O_{d,j}}.

A deterministic strategy sigma supplies a COMPLETE response table

    r_{d,j}: C_{d,j} -> Y_{B intersect O_{d,j}}

for every requested chart and owner. Call a strategy coherent if for every z in the certified joint context domain, all charts assemble exactly the same y_B. This test reuses the same table entry whenever the same local context recurs in different global contexts. Let F_B be the finite set of such coherent strategy tuples. For sigma in F_B let V_sigma(y,z) be the indicator of its common assembled output.

The exact common-response feasibility problem is

    lambda_sigma >= 0, sum_sigma lambda_sigma=1,
    K_B(y|z) = sum_sigma lambda_sigma V_sigma(y,z)
        for every certified (z,y).                         (19)

This is a linear program once the local views/observers are fixed. It SYNTHESIZES response tables and their common seed law; it does not pin arbitrary original latent seed encodings. Admissible input-dependent local recodings are already expressible by the allowed local response tables. If particular historical seed maps must be preserved, impose them explicitly as additional constraints and label the resulting obstruction as endpoint-specific.

**Exactness proof.** A feasible lambda is an implementation: sample sigma once, independently of current inputs; every component evaluates its declared table on its own view; coherence gives the common output, and (19) gives its law. Conversely, suppose an implementation uses one shared source and permitted private randomness, with the requested chart outputs equal almost surely for every certified context. For each shared source value, sample complete local private-random response tables for all finite contexts, retaining any correlations required by the proposed common implementation. They define a distribution on deterministic strategies. Since there are finitely many contexts and each equality holds almost surely, the set on which every equality holds simultaneously has probability one. The induced distribution is supported on F_B and satisfies (19). QED.

This converse concerns a COMMON IMPLEMENTATION, not merely separate implementations of identical marginal kernels. The latter need not yield a common response law respecting all local views, as the obstruction below shows. With unrestricted global input access and unrestricted source size, a common seed across actions alone is no restriction: independent action-indexed response tables can be packed into one seed. The force of (19) lies in the local-view reuse, recursion equations, and charged resource bounds.

For unrestricted finite shared randomness, private randomness can be absorbed into deterministic tables. This may increase the shared seed cardinality. For one fixed owner partition, a fixed-cardinality r source with independent free private coins instead requires a nonconvex mixture of r products of local channels; crossing charts need additional same-event/coherence constraints. Sparse deterministic support is sufficient but not necessary for that private-randomness resource model. Equation (19) by itself decides unrestricted finite-source feasibility; a bound on support size or source entropy is an additional, generally nonconvex constraint. Do not conflate these resource measures.

A feasible LP has a certificate with at most 1+|Z_B|(|Y_B|-1) strategy columns, by affine Caratheodory, or a smaller bound from the actual affine rank. Checking a sparse certificate is direct nonnegative summation. Finding it may require enumerating

    product_{d,j} |Y_{B intersect O_{d,j}}|^(|C_{d,j}|)

response tables before enforcing coherence. This cost is exponential in the local context/interface table sizes, not in the whole n-port history. It can still be prohibitive. Local permission/source constraints can make the feasible set empty; no physical implementation is claimed then.

Sample the certified source for each selected block once per tick, and reuse its event ID at every occurrence in every chart. Product independence across the selected blocks gives the one fixed learned joint kernel. Equations (18), correct initialization, and ordinary induction on time prove that every chart realizes that same learned controlled law. Combined with (15) or (16), this is a finite-data guarantee about the actual environment, conditional on (8), not just a simulator consistency result.

### A genuine incompatible crossing, not an arbitrary seed-label artifact

Let a,b be binary inputs and x,y binary outputs, with x uniform and x XOR y=ab. Chart 1 lets the x-owner see a and the y-owner see (a,b); it realizes the kernel with x=r, y=r XOR ab. Chart 2 lets the x-owner see (a,b) and the y-owner see b; it realizes the same kernel with y=s, x=s XOR ab.

A common deterministic strategy satisfying both chart descriptions would have x=f(a) and y=g(b), since corresponding outputs must agree at every (a,b). Its four parity equations are

    f(0) XOR g(0)=0, f(0) XOR g(1)=0,
    f(1) XOR g(0)=0, f(1) XOR g(1)=1.

XORing them gives 0=1. Thus F_B has no strategy that lies in the support of this kernel at all four contexts, and (19) is infeasible. Allowing arbitrary local source recodings does not fix it: the contradiction is about all allowable response functions, not about particular r/s encodings. Enlarging permissions or changing the common-refinement demand can fix it. This is the standard Bell/PR locality obstruction used as a regression test, not a new locality theorem.

The conditional-product class (8) includes this example as one two-output block with both inputs in its scope. Hence source/communication feasibility is a genuine additional stage even though statistical discovery and joint-kernel prediction succeed. The additive specialization excludes this contextual interaction and has the canonical full residual source as an easier witness.

## 14. Crossing memory and ownership without fictitious inverse maps

Two learned local observer summaries alpha(s) and beta(s) of the same observable suffix have a constructive synchronized refinement on the reachable image

    R = {(alpha(s),beta(s)): s is a legal local suffix}.

Its transition is the product of their updates driven by the same delivered record, and its projections recover the old summaries. If the two summaries use different scopes, use their union stream and charge both storage and added delivery. A noninjective summary is not inverted. The full Cartesian product can contain impossible pairs and is not automatically a realizable initialization.

For crossing output ownership partitions, split owned coordinates by nonempty intersections, carry these synchronized observer states, and retain each common source event ID. This constructs a joint operational refinement whenever the union interfaces and common-response LP are permitted. It need not preserve a smaller old source budget: for the uniform distribution on the three one-hot binary vectors, each bipartition has a binary shared-source implementation with group-private randomness, whereas the three-singleton refinement needs at least three shared-source values. Each positive product component supported on the three one-hot vectors must be a point mass: a Cartesian support containing two of them also contains a forbidden point. Three points therefore require three components.

The proposed maps are checked directly by (18) and (19); common refinement is an output of a finite feasibility problem, not an assumed universal lifting property. This one-hot budget obstruction is reused from the earlier Positive_Joint_Realization.md; it is a resource regression test, not a new lower bound. If the requested original C5 calculus uses ordered run substitution, a nonplanar crossing need not have any common C5 refinement even when this operational refinement exists. The exact scope of the source-level C5 bridge is stated separately in Witnessed_Feedback_Composition.md.

## 15. What the combined result advances, and what remains genuinely open

The combined theorem does not rest on a catalogue of all bounded programs plus a union bound. It constructs local conditional tables, learns unknown block/scope choices through finite support constraints, computes recursively closed observable quotients, checks executable local interfaces and a positive common-response law, and transfers a pointwise local-data certificate to every covered feedback controller. It avoids first constructing the n-port product state or enumerating feedback histories. The crossing-product estimate proved here in (13) is the bridge that allows unknown alternative block decompositions to remain coherent while still controlling the entire conditional law.

The concentration, automaton minimization, product coupling, response polytope, and constraint elimination ingredients are established mathematics. No novelty claim is made merely for combining their names. The defensible research deliverable here is the explicit end-to-end conditional theorem, local support/data/search accounting, executable witnesses, and a reproducible unknown-boundary/recursive-memory demonstration. Closest baselines and differences are catalogued in prior_art/Discovery_Baselines.md.

The observable-memory ceiling is a substantive restriction: it implies that a full length-L suffix would be sufficient in principle, even though no compressed sufficient state is supplied and no whole-state table is constructed. Thus this is not a theorem that discovers arbitrary hidden state with no observability premise.

The unresolved broad target is efficient recovery of arbitrary hidden recursive state and context-dependent shared latent topology from ordinary finite action/readout logs, with no finite observable-memory/sparse-factor universe, no observability/separation margin, and no quantified exploration coverage. Finite data cannot establish such a universe against unrestricted delayed or high-order alternatives. Even inside finite universes, arbitrary unknown ownership/encoder/source optimization can be computationally hard. The theorem does not silently replace those open problems by a supplied physical partition or a supplied sufficient state; it states exactly the unknown-structure class within which its local tests are complete.


## 16. Detailed accounting, sampling, and optional sharper transfer

Let A=|action alphabet| and k=|readout alphabet|. A width-s input context has at most A^s(Ak)^(Ls) values. The general statistical row budget can therefore be bounded by

    J_out <= [sum_{j=1}^b binom(n,j)]
                 [sum_{s=0}^{2bw} binom(n,s) A^s(Ak)^(Ls)].

The n^(b+w) block/scope catalogue is NOT the same as this roughly n^(b+2bw) conditioning-table cost. Computing and storing all conditional rows, acceptance factors, local suffix transitions, and source strategies must all be charged. For target local-cylinder probability rho, a sufficient raw endpoint count is obtained from (9) and the count bound in Section 2; its leading scale is

    O((log J_out + k^b + log(1/delta))/(rho eta^2)).

This is a statement about independent endpoint count. Every endpoint costs its actual reset/warmup/exploration length, and Stage-II rejection sampling additionally costs the reciprocal pre-output acceptance probability. If no quantitative positive acceptance bound is supplied, there is no finite guaranteed acquisition time. Union-context rho may itself be exponentially small in bwL; the theorem does not remove that information-theoretic cost.

The local recursion table for a selected scope U has at most (Ak)^(L|U|) raw suffixes. Its minimal learned quotient can be much smaller, but one should distinguish discovery-time local expansion from deployment memory after quotienting. The evidence gate can require more memory/access than the learned predictor and must be implemented by a separately charged monitor or included in the observer labels before minimization. A centralized safety monitor is not free local communication.

Empirical probabilities are rational. Exact sampling from a rational distribution can use a uniform integer plus rejection, with finite expected cost; it is not necessarily a bounded fair-bit sampler. A bounded-time finite-bit implementation requires a dyadic approximation or an allowed failure/overflow mechanism, and its TV error is added to the per-step kernel error. Exact rational LP witnesses also need a declared sampler. Real confidence-set weights are mathematical uncertainty parameters, not automatically executable physical random generators.

Totalize all proposed kernels and observers on a shared extended output alphabet. If an additive reconstruction emits an invalid value, map it to an explicit escape/failure symbol and stop or use the declared continuation. The true process is extended by zero escape probability. This deterministic mapping cannot increase the certified TV discrepancy. Thus an alternative positive law is not silently assumed to stay inside the physical support.

### KL refinement when the actual independent innovation blocks are recovered

In the additive subclass, suppose exact response recovery and the split-margin theorem recover the true blocks. Let Q_B be a positive learned residual law and assume calibration establishes KL(P_B||Q_B)<=kappa_B for each block. The entire residual vector has KL(P||Q)=sum_B KL(P_B||Q_B). Under any causal feedback controller, before coverage exit, output addition is the same deterministic translation in both models. The chain rule for relative entropy and equality of the controller's action kernel therefore give stopped-transcript KL at most H sum_B kappa_B. Pinsker yields

    TV(P_pi^stop,Q_pi^stop) <= sqrt(H sum_B kappa_B / 2).    (20)

The bound is simultaneous for every controller on the one calibration event, just like (15). It can be much sharper than summing block TV H times. For an unstopped deployment add beta_Q: maximally couple the stopped transcript laws and extend each by its conditional full continuation. If the stopped transcripts agree and Q does not exit, the full transcripts agree. Hence full TV is at most stopped TV plus beta_Q. This argument does not require replacing the KL estimate by a per-step TV bound.

A simple fully explicit sufficient local certificate is: if |P_B(y)-Q_B(y)|<=u_{B,y} simultaneously and every Q_B(y)>0, then

    KL(P_B||Q_B) <= chi2(P_B,Q_B)
                    <= sum_y u_{B,y}^2 / Q_B(y).           (21)

The first inequality follows from log x<=x-1 and normalization; the second is termwise. Confidence bounds for the cell probabilities can supply the u values. Zero empirical cells require smoothing or a separately proved zero physical mass; otherwise the displayed KL certificate is unavailable. The chain rule and Pinsker also apply in the reverse direction: simultaneous bounds on KL(Q_B||P_B) give the same square-root trajectory bound with Q and P interchanged in the entropy calculation. Empirical block laws have support contained in the true block support when the recovered partition is correct, which can make this direction convenient; its confidence proof is separate. This is not a generic KL claim for two different unknown block partitions.
