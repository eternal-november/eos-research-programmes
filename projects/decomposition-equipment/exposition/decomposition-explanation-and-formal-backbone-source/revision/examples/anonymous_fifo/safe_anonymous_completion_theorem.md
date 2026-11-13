# Safe acquisition, anonymous joint binding and useful completion

31 October 2026. **Final scoped synthesis, independently reviewed at the stated conditional mathematical/cost-envelope scope; see `mathematical_review.txt`. No hardware acceptance is implied.** The positive acquisition/schedule lemma is imported from `queue_acquisition_draft.md` (independently reviewed at its declared scope). The binding checker is imported from `binding_certificate_draft.md`, with its code/tests; its graph-scope proof and tests have independent review. The matched deadline obstruction is imported from `deadline_obstruction_draft.md`; its proof review and exact checks are recorded separately. No novelty, unrestricted discoverability, or one-shot end-to-end speedup claim.

## 1. Independent plant, observations and mission

For n addressed operation types, a world fixes a partition into FIFO servers and durations tau_i in (0,D]. Servers are independent, work-conserving and nonpreemptive. Routing and durations do not change between commissioning and production. Each request produces exactly one callback after completion, with delivery lag in [0,J]. Lag choices and payloads may be dependent across requests and time; no statistical inference or independence assumption is used in the positive theorem. Payloads do not affect routing, service duration or queue priority.

A callback exposes arrival time, its bit payload and its position in the raw stream, including observable ordering of equal timestamps. It exposes **no address/channel, request ID, capture/start/end metadata, source identity or persistent cross-frame rank**. A logged request address and release time are public action information, not a callback tag. Within a chosen production schedule, distinct release times establish FIFO order. The commissioning pair test is insensitive to simultaneous-request tie order.

The release grid constrains **request admissions only**: with quantum epsilon, all probe and production request times lie on epsilon*Z. Callback arrivals and computation may occur between these times. A separate trusted output/actuator capability permits post-read commands within its stated latency; it is not silently constrained to the request grid. D, J, measured duration intervals and callback times need not be grid multiples, and are represented with charged exact finite arithmetic.

Known primitives are a reliable clock/release API, D and J, a safe no-actuation commissioning mode preserving production routing/duration law, certified initial empty queues (or an independently justified bounded drain), callback reliability, storage/arithmetic capabilities, and physical tail bounds. These are trusted assumptions, not inferred from successful tests. Unknown initial backlog cannot be drained using D alone. Source/queue repeatability and calibration-to-production transport are supplied.

### Mission specified without reference to the learner

After a fixed externally declared commissioning deadline T0, burst b releases prescribed useful jobs, one per listed address. The role map rho(i) is supplied by the physical task, not inferred from callback values. The actual productive invocation i generates a bit x_i. For each role a the required command is

    ell_a = XOR_{i: rho(i)=a} x_i.

The command vector must be delivered before the burst's physical deadline after **all required productive jobs have run**, with final tail completed and budgets respected. Abort, missing jobs, wrong role output and late output count as missed/unsafe completion. Producing a tag, a substitute calibration sample or a cached earlier bit does not perform the prescribed fresh job.

**Independent physical bridge.** The known isolated sensor/load/interlock primitive couples each actual productive payload x_i to the corresponding role load exactly as above; timely commands equal to ell cause useful safe actuation and the declared safe tail. Incorrect commands have the independently stated violation/missed-work meaning. No physical hazard precedes the admitted exposure time while the bridge's gate is respected. Actual payload/load latches and safe isolation have a supplied retention lease covering the full proposed execution and final tail; waiting beyond that lease is not free. This is a supplied physical relation and capability, not a law learned from queue timing. There is no separate direct sensor for ell and no informative role-dependent calibration-success/hazard feedback through the safe diagnostic API. The predecessor's calibrated same-physical-sample reference sensor is not preserved by this selected API; giving an equally timely reference for ell could bypass anonymous association. If a real implementation does not satisfy this bridge, the theorem does not establish physical safety.

A single policy uses only the public request log, raw callbacks, trusted timing/capabilities and computation. It must work uniformly over the surviving physical worlds; it may not choose a different favorable source interpretation for different callbacks or obligations. The family is nonempty by the explicitly constructed fixtures below. The actual world remains fixed across every probe and burst.

## 2. Exact costed acquisition from raw anonymous timing

From idle, request i alone. Its only callback at elapsed time a_i gives

    L_i=max(0,a_i-J), U_i=min(D,a_i), tau_i in [L_i,U_i].

For every unordered pair with

    max(U_i,U_j)+J < L_i+L_j,                 (A)

issue the two requests simultaneously from idle and record only the maximum of their two callback times. Distinct servers give a maximum no greater than the left side; the same server gives a maximum no smaller than the right side. Hence a threshold in the strict gap identifies the relation without assigning either callback. If the gap is absent, return UNRESOLVED for this acquisition design; do not invent an edge. Consistency of the final relation is checked.

`queue_acquisition_draft.md` proves that tau_i>3J for all i guarantees every test has its gap under every allowed jitter trace. On this favorable class every comparison is correct and the partition is recovered. The theorem is exact under hard bounds; it has no confidence parameter.

Before request-grid rounding, the raw solo/pair waiting sum is

    A_raw = n(D+J) + binom(n,2)(2D+J).

It uses n^2 actual invocations, but is **not** by itself the implementation acquisition envelope. In particular D+J and 2D+J need not be legal next-release offsets. Let rho cover the independently supplied physical drain/tail after a probe, and C_probe cover charged per-probe readout, validation, dispatch/setup and endpoint guards. With request quantum epsilon use whole slots

    R1=epsilon*ceil((D+J+rho+C_probe)/epsilon),
    R2=epsilon*ceil((2D+J+rho+C_probe)/epsilon).

Each slot starts with its solo or simultaneous-pair admission on the request grid and reserves through the drain, arithmetic and next-issue preparation. At an exact endpoint all callbacks and required guards are processed before another request is issued; any strictly positive guard belongs in C_probe. Initial setup or independently bounded drain is rounded to R_init=epsilon*ceil(C_init/epsilon). Final partition validation, schedule computation and compilation have a separate certified bound C_compile; reserve R_compile=epsilon*ceil(C_compile/epsilon) before production readiness. Thus a conservative grid-aligned envelope is

    A_tot=R_init+n*R1+binom(n,2)*R2+R_compile.

Use larger type-specific envelopes if the common bounds do not apply. Every added rounding interval is elapsed physical time and charged. The predeclared commissioning deadline T0 and subsequent burst starts must be grid-aligned, or the wait to the next legal start is additionally charged; they are not chosen after favorable observations. Storage and other non-time resources have separate capacity checks. Merely refusing after expensive acquisition is not free. This is deterministic hard-bound accounting, not a confidence estimate.

## 3. Joint binding certificate from actual production callbacks

For a chosen legal production request schedule with a certified empty initial queue and known within-queue request order, propagate bounds along that queue. If its kth request is released at r_k, actual completion obeys C_k=max(r_k,C_(k-1))+tau_k. Set lower completion l_k=max(r_k,l_(k-1))+L_k and upper completion u_k=max(r_k,u_(k-1))+U_k, with both initial bounds equal to the known empty start time. Monotonicity of max and addition proves l_k<=C_k<=u_k by induction. Thus I_k=[l_k,u_k+J] contains its actual arrival even for dependent jitter and fixed shared parameters. A schedule with unresolved same-server tie order must retain all tie orders or use a conservative enclosing window; it may not secretly choose the favorable one.

The production observation horizon is closed: no unexplained carry-in callbacks, exactly the prescribed requests, all their callbacks received before the known upper horizon, and no carry-out callbacks omitted. Reliability and one-report-per-request give one actual global bijection between these jobs and these report occurrences. Together with the interval induction, every edge of this actual bijection belongs to G. This proves the binding checker's coverage premise rather than postulating joint records. Collect the n actual callbacks, retaining their arrival times t_r and payloads y_r. Build a bipartite graph G on invocation vertices i and raw callback-occurrence vertices r, with edge (i,r) iff t_r belongs to I_i. A callback occurrence is a position in this actual public stream, not a stable source label.

The physical callback bijection is a perfect matching of G whenever the acquired facts and timing propagation are sound. Thus G has at least one perfect matching. An empty matching set causes inconsistency/refusal, never vacuous certification.

For a perfect matching M, define its required role vector

    v_a(M) = XOR_{(i,r) in M: rho(i)=a} y_r.

Accept a command vector v only if every perfect matching gives the same v. The actual matching is among them, so accepted v equals the actual physical role-load vector ell. This is one simultaneous matching, not independently chosen packet identities.

**Sound relaxation, not full-world completeness.** Marginal delivery windows can admit matchings with no jointly feasible fixed durations/jitters. Their universal agreement is sufficient; disagreement returns UNRESOLVED unless a separate proof exhibits actual incompatible worlds. It is not a certified NO.

### Imported polynomial parity-invariance checker

Use the proved graph theorem in `binding_certificate_draft.md`. Find one perfect matching m. On job vertices put an arc i->j whenever report m(i) is compatible with job j, with vector weight

    w(i,j)=y_(m(i)) (e_(rho(i))+e_(rho(j))) in F_2^g.

All graph matchings give the same role vector exactly when every directed cycle has zero XOR weight. Indeed any matching differs from m by disjoint permutation cycles, and any individual directed cycle can be flipped to a graph matching. Within each strongly connected component this is equivalent to potentials p_i satisfying w(i,j)=p_i+p_j on every internal arc; root/return paths prove the converse. Cross-component arcs cannot occur in an alternative matching and impose no potential equation.

The checker returns a baseline matching, role vector, recomputed SCCs and checked potentials, or two graph matchings with differing role vectors. The latter remains UNRESOLVED physically. No perfect matching means model/evidence inconsistency. The implementation constructs a nonzero simple cycle from any failed potential check before claiming a second graph matching; it does not mistake a formal inconsistent edge for a feasible cycle.

For m_G graph edges and g represented roles, its conservative graph bound is O(n(n+m_G)+(n^2+m_G)g) elementary index/vector operations, with polynomial index/path storage; each vector has g bits and indices require O(log n) bits. Building G costs n^2 exact endpoint comparisons. Rational time values of B-bit representation use charged integer arithmetic, not a real-number oracle; endpoint-sum growth and role-label encoding are included in the input/capability bound. The hardware checker envelope C_bind must implement these costs, not merely quote polynomiality. `binding_checker.py` and `test_binding_checker.py` provide the checked reference implementation and finite validation; the general argument supplies theorem scope.

A simple sufficient specialization checks that each callback's allowed edges reach only one role and that a perfect matching exists. Any matching then assigns that callback to the same role. Full individual binding is unnecessary: two callbacks can interchange between two same-role jobs while the role parity remains fixed. Their physical origins remain genuinely unidentified; a later task requesting their separate role outputs can require more information.

## 4. Explicit schedule guaranteeing acceptance on a growing class

Let the recovered partition have q queues, each containing at most h productive jobs. Form the global enclosing bounds

    L=min_i L_i, U=max_i U_i, W=U-L.

This is an enclosing union range, not an intersection and not a claim that durations are equal. With supplied release quantum epsilon>0, compute Delta=epsilon*(floor((hW+J)/epsilon)+1), the smallest positive grid multiple strictly above hW+J. Then test

    Delta > hW+J,
    L > (q-1)Delta+hW+J.                     (S)

For queue r=0,...,q-1, issue its first actual job at rDelta. Issue its subsequent jobs in a known strict FIFO order before rDelta+L; for a legal release quantum epsilon, offsets (k-1)epsilon suffice when (h-1)epsilon<L. Any global dispatch-port collision or simultaneous-issue capacity is checked against the actual capability inventory. These issues and their computation are not zero-time by convention.

The k-th completion in queue r is a sum of k admitted durations, with no intervening idle gap. Its callback window is

    I_rk=[rDelta+kL, rDelta+kU+J].

Within each stage, adjacent windows are disjoint because Delta>kW+J. Between stage k and k+1, they are disjoint because L>(q-1)Delta+kW+J. Thus (S) separates every window, including omitted jobs in shorter queues. The actual callback matching is unique and the general checker necessarily accepts. Stable callback rank was not supplied: association follows from the experimentally acquired partition, measured bounds and controlled schedule.

All callbacks arrive by

    T_arr=(q-1)Delta+hU+J.

Add actual readout processing, graph/checking, command delivery, actuation and final-tail bounds to obtain T_service. Implementations may use the unique-window specialization rather than general matching checking, but this switch is explicitly checked and costed.

### Favorable fixture and nonemptiness

For n=qh with q>=2, take any unknown partition into q queues of h jobs. Let actual durations all happen to equal tau; equality is fixture truth, not learner input. Arbitrary allowed solo jitters give L>=tau-J, U<=tau+J and W<=2J. The executable selection gives Delta<=hW+J+epsilon<=(2h+1)J+epsilon. Consequently the inequalities are guaranteed for every commissioning jitter trace if

    tau > q(2h+1)J+(q-1)epsilon+J,
    tau>3J, tau<=D,

and legal within-queue enqueue/dispatch margins hold. Choosing D and tau accordingly gives arbitrarily growing interacting families. Unknown callback payload laws/source coupling remain unlearned. For an explicit interacting fixture choose q>=2 and h>=2, h distinct physical roles, and one job of each role in every true queue; role labels are known on addresses, while the queue partition is not supplied. Each role load is the parity of q actual payloads produced across different queues, and the mission requires the entire h-role vector, not the permutation-invariant global parity. The general algorithm is not given this rainbow arrangement and does not use it as an identification premise. This specifies nontrivial cross-queue composition without asserting that no task-direct alternative policy can solve it.

## 5. End-to-end completion theorem at the stated scope

Fix the physical class, independent role-load mission, legal releases, hardware cost bounds, fixed T0 and K prescribed production bursts. Suppose:

1. The actual world satisfies the trusted semantics. For the particular complete commissioning/service trace under consideration, all acquisition gaps (A), measured schedule checks (S), legal dispatch and strict enqueue feasibility pass.
2. Initialization and A_tot finish by T0; every probe is safe under the independently supplied gate/tail envelope.
3. Every burst is released only after commissioning, and its production latency allowance covers T_service. Bursts are separated by the full required drain/tail; no backlog is silently discarded.
4. All initial resource budgets cover acquisition, all K production bursts, storage, finite arithmetic/checker work, commands, tails and any idle waiting. In a simple consecutive-burst calendar of length H>=T_service, the elapsed-time budget covers T0+KH, not merely A_raw+K T_arr. Other calendars use their actual final timestamp.

Then, **pointwise on that complete trace**, the described single observation-based controller safely completes all K missions. Acquisition obtains the true partition and enclosing durations; (S) guarantees every actual callback has its unique window; the accepted role vector equals ell; the independent physical bridge gives useful safe actuation and tail. All costs fit by the declared inequalities. This pointwise result does not assert that every commissioning trace in the same world passes its data-dependent checks.

**Uniform completeness corollary.** Restrict to the favorable world class of §4 whose truth-level strict inequalities guarantee, for every allowed commissioning jitter trace, all acquisition and schedule checks, clock/dispatch feasibility and the predeclared implementation/deadline envelopes. Fix budgets large enough for the corresponding worst-case acquisition/service bounds, not only a favorable observed instance. Then the same controller accepts and safely completes all K bursts for **every** allowed commissioning and service jitter/payload realization in each such fixed world. The earlier derivation W<=2J, L>=tau-J and U<=tau+J proves the numeric readiness part without assuming its discovery. Refusal is counted as failure outside that class, so the uniform corollary has no accepted-runs-only loophole.

Outside these sufficient conditions, the algorithm can return UNRESOLVED or miss its mission; refusal is not counted as a successful outcome. It does not establish all-policy impossibility. For other schedules, the universal-matching certificate can also accept genuinely ambiguous individual bindings. A physical example consists of two independent equal-duration queues, J=0, simultaneous release, two same-role jobs and an unknown persistent equal-time callback tie priority. Both physical priorities yield the same observed raw bit pair but reverse the possible job binding; the two jobs' actual role load is their XOR in either case. The all-matchings checker accepts without identifying priority. This is a physically feasible within-role ambiguity, unlike an arbitrary abstract graph example that need not come from interval windows. Its soundness is unchanged, but this explicit completeness guarantee uses the separated-window schedule.

## 6. Matched deadline obstruction and same-hardware repair

Import `deadline_obstruction_draft.md`, whose full legal-information and backlog proof is part of this synthesis. Its independent proof review is tracked separately. The witness consists of two independent queues, duration tau=Q, J=0, grid release times Q*Z and a certified empty initial grid state. Queues are nonpreemptive. Equal-time callbacks form an observable ordered stream with persistent unknown tie priority pi. Every invocation has an uncontrollable fresh independent fair payload; service payloads do not exist before their productive jobs release at zero. There is no payload pilot, prefetch, reread, direct role-load oracle or duplicate useful invocation. Calibration grants only the safe callback API, not dangerous role-dependent physical feedback.

All executable adaptive calibration and backlog strategies are admitted. Conditional on every public action history, completion times and counts depend only on queue service and grid admissions. Untied callbacks are fair; tied callbacks form an ordered iid fair pair under either pi. Coupling bits by public report position proves identical complete observable histories under both priority worlds, including adaptive stopping and serial probes.

Starting empty on the Q-grid, all service starts and completions remain on the grid by C=max(release,previous finish)+Q. Every positive residual backlog delay is at least Q. The Q-grid governs requests only; the same hardware separately supports callback reading/computation and an asynchronous output pulse within gamma<Q. With that output allowance and deadline Q+gamma<2Q, any successful policy must start both fresh jobs at zero. This includes policies that leave calibration backlog: any positive work ahead forces missed work. Jobs behind the productive job cannot yield extra useful reports before the deadline.

On the event E that both jobs start at zero, let (X,Y) be their ordered Q-time report bits. The required role vectors are (X,Y) and (Y,X) in the two worlds. They differ with probability 1/2. Granting the controller its complete raw history through the deadline cannot increase the sum of its two conditional success probabilities beyond 3/2: when X=Y both worlds can succeed, and when X!=Y at most one can. On the complement of E neither world completes. Thus every common policy has average and worst-world missed/unsafe risk at least 1/4. A fair private priority guess attains risk 1/4 in each world; this is a combined-loss comparator, **not a hard-safe policy**. A hard-safe policy must refuse differing-bit traces and completes at most half the time. Refusal is counted as missed work.

The informed-pi controller has identical hardware and budget, starts both actual jobs at zero, reads the same callbacks and correctly actuates by Q+gamma for every payload pair. It knows no future bits. Therefore this is a real mission-policy obstruction, not merely different inferred interfaces.

The original negative-fixture hardware already safely retains its loaded bits under isolation through 2Q+gamma and the declared tail, even though its initial mission deadline is earlier. Subject to that unchanged retention capability, changing only the deadline to 2Q+gamma permits releases at zero and Q. Callbacks at Q and 2Q bind the fresh jobs uniquely; storing the first bit and computing the role vector gives zero-risk completion without learning pi or adding tags. All service, storage and actuation costs are charged. This is a sufficient one-quantum repair, not a claim that Q is the minimum real-valued slack increase when computation can be faster than gamma. Every deadline strictly below 2Q retains the start-time obstruction.

These two worlds satisfy the queue-acquisition separation premise (J=0,tau=Q>0); indeed their partition may already be known. Their failure is a binding/deadline obstruction in the same physical class, not failure of queue identification or departure to an unmodelled stochastic source class. The source symmetry is a particular lawful payload distribution used to prove the bound.

## 7. What changed from the actual predecessor, and what did not

The recovered assurance structured telemetry lemma §B explicitly observes packet tags and accurate delivery times; its executed queue trace returns `(channel, arrival, start, end)`. The prior linear coupling theorem supplies known physical projection/capture maps A_e and H+D block coordinates. Both already learn substantial queue/capture/source structure and mission-sufficient partial interfaces. The operational certificate bridge already permits persistent alias/sensor-map alternatives, and the finite-signature theorem already gives an exhaustive existence baseline. None of those achievements is claimed as new here.

**This is not the entire predecessor platform with only tags deleted.** Its calibrated physical references and same-sample observations are not transported into the selected callback-only API. The new independent role-load primitive has no supplied direct readout, and safe diagnostics expose no informative role-dependent physical success feedback. Such extra capabilities could defeat the obstruction or bypass binding. See `comparison_delta.md` for the exact assumptions comparison.

Within this selected API, this construction removes callback origin/channel/request/start/end fields and does not replace them with a stable anonymous rank. It supplies a raw anonymous max-time acquisition step, then synthesizes dynamic association through a controlled release schedule or an all-matchings certificate. Trusted timing, FIFO/reliability/repeatability, addressed command semantics, safe isolation and the physical payload-to-load bridge remain strong prerequisites. Hard jitter bounds are not statistically learned. Unknown payload source ontology is neither inferred nor required.

## 8. Fair baselines and nonclaims

- **Controlled tagged comparator:** the NEW selected FIFO hardware, role-load bridge, task and budgets, with callback-origin metadata added. It is not a claim that the older telemetry platform had identical sensing capabilities. Tags eliminate the anonymous association duty; they do not eliminate service feasibility or physical costs. Do not compare against a weaker artificially delayed tagged controller.
- **Serial/drained service:** legal singleton requests unambiguously reveal each invocation. Charge their actual n-job duration, drain/dispatch/checking and deadline. They may solve the mission when latency permits. Commissioning itself costs at least n*tau on the equal-duration fixture, so no one-burst end-to-end speedup is claimed.
- **All-address staggering:** after solo timing bounds, stagger every address without learning the partition. It can succeed in favorable worlds and must be evaluated, not ruled out by definition. This result does not prove partition learning necessary for every policy.
- **Task-direct prediction/regression:** a method may predict the required role aggregates directly without identifying queues or individual bindings, when the same raw evidence and assumptions support such prediction. It must be compared on the same safe acquisition, observation, deadline and error budgets. This construction proves no superiority or necessity against all such methods.
- **Finite-world/signature or global game enumeration:** prior existence machinery can represent binding alternatives. The present contribution is an explicit anonymous physical acquisition, a small timing certificate and costed mission use, not first general decidability or a claim that enumeration cannot work.
- **Matching and active identification:** use standard algorithms with their proper hypotheses. Partial identification sufficient for a task is not itself a novelty claim.

No categorical structural decoration is required for the operational theorem. An I1/I2/I5 or cylinder bridge may be added only if actual carriers, maps, joint records and resource meaning are proved, not as a substitute for acquisition or mission soundness.
