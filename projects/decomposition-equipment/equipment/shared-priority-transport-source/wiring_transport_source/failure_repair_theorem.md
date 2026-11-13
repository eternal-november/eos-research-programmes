# Local evidence obstruction and costed shared priority repair

31 October 2026. A conditional construction showing that local certificates alone do not establish the shared-resource mission. This is not an impossibility of joint experimentation and is not a novelty claim.

## Result first

Under the explicitly supplied one-commit-per-tick batch interface below, for every n>=2 there are n! physically distinct shared-arbitration worlds with identical complete isolated-module observations and valid identical intrinsic-service FIFO certificates. A known single shared resource replaces separate availability, not an unknown old queue partition. In a saturated fresh-job mission, those worlds give the same anonymous callback timing law but require different physical role commands. For uniform unknown arbitration and fair actual payloads, every local-information-only policy has average success at most (n+1)/2^n, including policies admitting extra jobs. The sharp hard-safe completion rate 2^(1-n) is claimed only for productive-only commits with no extra jobs. Safe joint timing experiments on the **same declared fast/slow address API in this construction** recover the arbitration; n(n-1)/2 elementary comparisons suffice, and adaptive sorting reduces this to O(n log n). All probe service, grid rounding, drain, computation, storage, retention and production tail must be budgeted as below. Ordinary drained serialization is explicitly legal and repairs the mission when its longer deadline is supplied.

The fast/slow operation choice is a richer API than the predecessor callback-only model. It controls intrinsic demand, not payload bits. Both the failure and the repair use this same newly declared interface; the repair is not asserted for the predecessor hardware unchanged. Atomic batch admission before dispatch and productive-work invariance under wiring are likewise supplied capabilities.

## 1. Plant and identical local facts

There are n modules. Module i has two addressed operation types P_i and D_i, in one known local FIFO. They have fixed intrinsic service demands Q and 2Q, respectively, Q>0. Addresses, FIFO membership, duration facts, one-callback-per-invocation reliability and J=0 are the same in every world. Raw callbacks have time, payload and stream occurrence, but no source tag or grant metadata. Every invocation's payload is an uncontrollable independent fair bit. The actual useful invocation P_i supplies the bit for physical role i under the predecessor's same isolated load/interlock bridge. Probe bits are not substitute productive bits, and there is no extra role oracle or pilot.

A local certificate must say exactly what survives wiring. Each local FIFO preserves admission order; once its head is granted the server it executes nonpreemptively for its certified intrinsic demand; callbacks follow completion without lag. When continuously granted from an empty state, its measured isolated timing recurrence is valid. The shared context may delay the **grant** but never changes work demand or local order. These are open-interface/conditional timing facts, not a retained unconditional wall-clock promise. The availability/noninterference semantics are a trusted structural interface of the hardware, not something finite isolated tests alone infer. If the earlier certificate literally promises wall-clock completion <=Q after admission regardless of availability, it does NOT remain valid: this construction cannot honestly be used to claim that stronger preservation.

The supplied admission interface permits at most one atomic batch commit per legal tick, enforced globally across modules; an empty commit also consumes that tick. An equivalent implementation collects the complete tick batch before any dispatch. There is no second same-tick commit after arbitration starts. This is a physical/API premise, not a restriction on which permitted policies are considered.

Known wiring: a single nonpreemptive, work-conserving physical server serves all modules. On each idle transition it selects the highest-priority nonempty module, then runs that module's FIFO head to completion. The unknown fixed context parameter is a strict priority permutation pi of the n modules. No unknown partition remains: local FIFOs and the one shared arbiter are known. All modules retain their local order and exact granted-service facts in every pi-world.

Any complete adaptive local experiment which never has work pending in two modules at once is pi-blind. Its timings depend on its chosen module demands only; its observed bits are iid fair. This includes unlimited singleton tests, FIFO tests within each module, ordinary fully drained calibration, and stopping decisions based on those observations. Couple bits by callback occurrence to obtain equal public histories pathwise. The distinction is contention, not an arbitrary prohibition of useful serial tests.

## 2. Tight production mission admits serialization but defeats its deadline

Use the same admission quantum R=nQ in every world. The release API supplies atomic batch admission: at a legal clock tick the entire submitted batch becomes queued before the arbiter makes its next idle-resource selection. The primitive supports batches of at least n requests, with certified setup completed before the tick. Equal numeric timestamps on separately processed submissions are NOT sufficient. The identical primitive applies to diagnostic and productive batches in every world. At most ONE batch commit, including an empty commit, is permitted at each legal tick; after that commit the next admission opportunity is the next tick. Thus separate singleton commits at the same numeric timestamp are not legal. This is a strengthened declared API premise, not implied merely by atomicity. If repeated same-tick commits were allowed, admitting one singleton first and the other after its dispatch would defeat the n=2 priority-binding obstruction without delaying admission time. Actual useful P_i jobs become available at time 0 and may not be substituted, prefetched or rerun. They require n separate role bits. Provide certified empty queues at 0, or admit all backlog strategies in the argument below. The independently declared mission deadline is

    H=nQ+gamma,  0<gamma<Q,

where gamma pays callback readout, assignment/checking, output delivery, physical actuation and required final tail under a supplied implementation bound. This must be achievable for the selected n; gamma is not an uncharged real-number computation assumption. A family of increasingly provisioned hardware instances may supply that bound, or Q can grow with the certified O(n) processing/tail cost.

Every useful job must be admitted in the SAME unique batch commit at 0: the next legal positive admission is R=nQ, whose earliest completion is nQ+Q>H. All n useful jobs occupy the resource for exactly nQ. An extra complete diagnostic before their completion would add >=Q and miss H. Queue/service endpoints are multiples of Q because admissions are multiples of nQ and demands are Q or 2Q. Therefore any positive residual calibration work at 0 costs at least Q and also misses H. Calibration jobs behind all useful jobs cannot complete before H or reveal useful arbitration evidence in time. If initial queues are certified empty, the residual argument is unnecessary.

Conditional on successful start of all useful jobs at 0, callbacks arrive at Q,2Q,...,nQ, regardless of pi. Denote their actual ordered payloads y=(y_1,...,y_n). The required physical role vector is the vector assigning y_k to the module occupying priority rank k. This is genuine task binding, not only a dispute about inferred interfaces. A controller informed of pi uses identical hardware, receives no future bits, and always completes by H under the charged gamma envelope.

With only local information, pi remains unrestricted. First consider a productive-only commit with exactly the n required jobs and no extras. For uniform pi and iid fair bits, the ordered observations y are independent of pi. If y contains k ones, the physical role vector is uniform on the binomial(n,k) possible vectors with k ones, conditional on all the public evidence. A common policy's conditional success is <=1/binomial(n,k). Averaging gives

    average_pi success <= sum_(k=0)^n [binomial(n,k)/2^n]/binomial(n,k)
                      = (n+1)/2^n.

Thus some fixed pi has missed/unsafe risk >=1-(n+1)/2^n. A random uniform permutation guess using a productive-only commit attains this risk in every world, but is not hard-safe.

The combined success bound remains valid when a policy includes arbitrary extra diagnostic or calibration jobs. Use a virtual pure-productive run extension: couple each world's actual useful bits to the corresponding pure-productive priority-order trace, independently of pi. In every world where the original policy completes on time, no extra work can have completed before the last required job, since it would consume at least Q beyond the nQ useful demand. The observed trace through the deadline in that successful world therefore agrees with the pure-productive trace. Define an output rule on every virtual pure-productive trace by applying the original policy, completing the rule arbitrarily when it would not issue a command. The original successful world/bit pairs form a subset of this rule's successful pairs. The pure-productive counting bound above bounds that larger set by (n+1)/2^n. This argument does not incorrectly assume a uniform priority posterior after conditioning on successful execution; extras can filter worlds through their failure timings.

The sharper hard-safe statement has a narrower scope: for a manifest restricted to a productive-only commit, an unrestricted-pi hard-safe policy can command only when all observed bits agree, and its optimal completion probability is 2^(1-n). Refusal counts as missed work. For n=2 the combined-loss risk bound is >=1/4, and the productive-only hard-safe completion bound is <=1/2. No sharp hard-safe bound of 2^(1-n) is asserted for arbitrary-extra-job policies, whose diagnostic timing failures can filter the surviving worlds.

This lower bound does not include a controller that already ran an informative joint calibration: that is the intended repair. It is specifically a theorem that identical valid local certificates/history are insufficient for this global mission. It must not be advertised as an all-safe-experiments obstruction.

## 3. Same-API safe joint experiment

From certified drained idle, use the tick's single allowed atomic batch commit to admit D_i (demand 2Q) and P_j (demand Q), i!=j. If i outranks j, callback times relative to admission are (2Q,3Q). Otherwise they are (Q,3Q). The first time determines the priority relation exactly, without attributing either anonymous payload or controlling its value. The unequal demands are existing locally calibrated operation addresses, not new metadata/sensing hardware. The total callback horizon is 3Q in both cases. Both probes are under the same known no-actuation gate, safe tails and production-preserving arbitration semantics.

All pair comparisons recover pi after m=binomial(n,2) tests, with a consistency/total-order check. A comparison sorting algorithm can instead choose pairs adaptively, using at most m_sort<=n ceil(log_2 n) comparisons under a conservative deterministic comparison bound. This reduces actual invocations from n(n-1) to <=2n ceil(log_2 n). Each binary comparison supplies at most one bit; any decision tree that must distinguish all n! priorities needs at least ceil(log_2(n!)) comparisons in the worst case. This lower bound is for this binary-comparison experiment model, not all possible multiway temporal experiments.

Once pi is known, simultaneous productive admissions at 0 are safe: the kth callback binds to pi's kth module. No inference of payload ontology is needed.

## 4. Complete envelope and retained physical assumptions

Let C_init cover independently justified initial draining/setup; rho_probe cover physical post-probe tail/drain; C_probe cover both callback handling, exact time comparison, dispatch preparation and all endpoint guards; C_compile cover sorting/consistency, storage construction and production readiness. All are independently certified elapsed-time envelopes, not free operations. For common admission quantum R=nQ reserve

    S_init = R ceil(C_init/R),
    S_pair = R ceil((3Q+rho_probe+C_probe)/R),
    S_compile = R ceil(C_compile/R),
    A_joint = S_init + m S_pair + S_compile.

Use m=binomial(n,2) or the certified sorting worst-case bound. Every probe starts at a legal slot boundary; callbacks, tails and readiness guards must be processed before the next issue. If a zero guard is physically impossible, include the positive guard in C_probe. Atomic admission of the diagnostic pair and of the n-job production batch requires the supplied admission-before-dispatch primitive above. Charge batch construction, port/buffer capacity, pre-tick submission/setup, and any hardware guard in C_probe, C_compile, and the production preparation budget as applicable. If submission itself consumes elapsed time before admission, reserve it before the declared release tick; fresh payloads are generated only by the actual release/execution, not this preparation. If hardware instead dispatches after the first individual submission, even when all submissions share a timestamp, this witness and the diagnostic decision rule do not apply without a fresh proof for that event order.

If local learning is not already paid, singleton P_i and D_i probes can measure Q and 2Q exactly at J=0. Before observing them, the implementation must already possess certified upper bounds D_P>=Q and D_D>=2Q (or type-specific public caps); it cannot use the unknown true Q as its initial safe wait horizon. With the corresponding local safe tail/handling costs, add

    A_local = sum_i R ceil((D_P+rho_P+C_P)/R)
            + sum_i R ceil((D_D+rho_D+C_D)/R)
            + charged local validation/setup.

The exact learned Q may be used for the joint 3Q horizon only after successful local validation. R is a supplied physical admission quantum; R=nQ specifies the witness family and need not be used to infer the duration before measurement. That uses 2n local invocations; A_joint uses 2m additional invocations. No invocation can count as one of the mission's fresh P_i jobs. Different timing/error models require their own interval separation test; the exact first-arrival decision here is only claimed for J=0.

Fix commissioning deadline T0 independently, grid-aligned, and require A_local+A_joint<=T0 (or A_joint<=T0 if local costs are explicitly sunk). Production finish is T0+nQ+gamma for one burst; K bursts require their actual scheduled last timestamp and any extra idle/drain. Resource checks include 2n+2m+Kn invocations when local probes are needed, charged arithmetic and dispatcher capacity, O(n log n) bits for stored permutation/inverse, O(n) productive payload bits, sorting working storage, all command/tail energy and idle waiting. Probe storage can stream except the retained order/comparison evidence required by the chosen proof checker. Retention/isolation leases must cover each probe horizon/tail and the complete production latency; acquisition cannot silently hold expired useful loads because no useful load yet exists before its fresh mission release.

## 5. Legal serialization and exact task-relative criterion

Uninformed ordinary serialized production is permitted: admit P_i alone at (i-1)R, receive its uniquely bound callback at (i-1)R+Q. It completes at

    H_serial=(n-1)R+Q+gamma,

if the SAME hardware's previously supplied isolation/retention capability covers that interval, the wider mission deadline is authorized, and storage/idle costs are paid. It is not intrinsically forbidden or unsafe. For n=2,R=2Q this is 3Q+gamma versus informed/shared-burst 2Q+gamma. There is no end-to-end speedup assertion: joint commissioning can dominate a single mission, while repeated bursts may amortize it. Draining cannot reveal priorities by itself because it removes contention.

For any remaining priority set Pi and a saturated simultaneous batch with known mapping rho from modules to physical roles, the exact binding criterion on observed y is:

    v_a(pi,y) = XOR_(k: rho(pi_k)=a) y_k

must be identical for every pi in Pi, for all required roles a. Every pi is an actual feasible world; this is not an interval-graph relaxation. A universal all-payload guarantee holds iff, for every rank k, rho(pi_k) is constant over Pi. Necessity follows by choosing y with just coordinate k equal to 1; sufficiency follows by linearity. Thus distinct role per module demands exact pi, whereas a single global-parity role needs no arbitration information. This criterion generalizes the counterexample beyond n=2 and explicitly allows task-sufficient partial context learning.

## Scope and limitations

* Worlds differ only in fixed shared arbitration; no unknown partition is relabeled as a new phenomenon.
* The shared context affects grant delays and task-role association. Local intrinsic service/FIFO facts remain true; unconditional isolated wall-clock promises do not.
* Sparse timing experiments cannot establish stationary arbitration or physical noninterference; these remain declared transport assumptions.
* No new tags, controllable payloads or reference sensors are introduced by repair.
* The deadline obstruction uses a coarse fixed admission grid PLUS the explicitly strengthened one-atomic-commit-per-tick admission protocol; the latter is not inherited from the predecessor merely by specifying a grid. Repeated same-tick commits can defeat the two-module obstruction; with arbitrarily fine zero-cost admission staggering, this particular negative theorem need not survive.
* The known bridge, gate and retention are unchanged across priority worlds and repair. Longer-deadline serialization additionally requires a lease already supplied for that length, or it is not an available repair.

## 6. Exact partial-order transport law

Suppose priority evidence is a finite strict poset P on modules and its full linear-extension set is the remaining physically feasible order set. This latter coverage/equality premise matters: pair observations in the specified unrestricted-priority plant give it, whereas arbitrary multiway histories may impose more than poset constraints.

Then the simultaneous batch is uniformly role-bindable for all possible payload vectors iff every incomparable pair in P has the same physical role.

Proof. Any two linear extensions are connected by adjacent swaps of incomparable elements (move the first differing desired element left across only incomparable predecessors, induct on the remaining suffix). If all such pairs have the same role, each swap leaves the sequence of roles by service rank unchanged, proving sufficiency by §5. Conversely, for an incomparable pair i,j with different roles, there is a linear extension in which they are consecutive: order the union of their strict predecessor sets first, then i,j, then the remainder. Neither is in the predecessor union of the other, and the union is a down-set. Swapping i,j gives another valid extension with two consecutive rank roles reversed. Set the observed bit at one of those ranks to 1 and every other bit to 0. Both actual worlds give that same timed payload trace with positive probability, but their required role vectors differ. This proves necessity using actual worlds, not abstract graph matchings.

Operational certificate: validate acyclicity, compute reachability/transitive closure, then check every incomparable pair's roles. Keep one topological order to assign observed rank payloads. The certificate may leave all within-role order unknown. Cost a concrete finite implementation: O(n^3) Boolean operations and O(n^2) reachability bits for elementary closure, plus O(n^2) role comparisons and O(n) payload/parity processing (or a faster certified implementation). Compile-time closure belongs in C_compile; per-burst role aggregation belongs in gamma. For disjoint evidence sets under additional wiring, union their directed constraints, recompute closure and reject cycles; only if the union's linear extensions still exactly cover feasible context orders may this same criterion be treated as exact. A sound overapproximation still gives sufficient, not necessary, acceptance.

Unrestricted multiway diagnostic batches can yield multi-valued timing outcomes and can outperform binary-comparison information counts. No all-legal-probe optimal acquisition bound is asserted. The local-only observational equivalence is exact over all local/drained adaptive probes; the safe joint algorithm is a constructive sufficient repair with full charged costs.

### Finite independent check

Executed exhaustive enumeration over every forward-edge DAG on n=2,3,4 labeled vertices and every binary role assignment (1,096 DAG/role fixtures). Enumerated all linear extensions and confirmed equivalence between invariant role-by-rank sequence and the incomparable-pair criterion in every fixture. Forward-edge DAGs cover every finite DAG up to a topological relabeling. Also checked the success-bound summation for n=2,3,4, yielding 0.75, 0.5, 0.3125. These checks supplement, not replace, the general proofs.

The reproducible standard-library script `check_failure_repair_posets.py` additionally checks the stronger fixed-payload criterion derived in `transport_theorem.md`: for every cross-role incomparable pair x,y, require b_k=b_(k+1) for all integer adjacent-rank positions from |Pred(x) union Pred(y)|+1 through n-|Succ(x) union Succ(y)|-1. Exhaustive comparison against actual role-vector invariance over every linear extension passes 16,928 DAG/role/payload fixtures for n=2,3,4. This permits accepting particular payload traces even when the uniform all-payload certificate fails.

For a separate growing-family obstruction under the weaker interface allowing multiple same-tick commits, see `relaxed_admission_bound.md`. That argument must not be substituted silently for this source's one-commit proof or its productive-only hard-safe sharpness claim.
