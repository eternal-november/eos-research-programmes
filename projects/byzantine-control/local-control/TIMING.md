# Constructed finite scheduling for local maintenance

Status: derived conditional timing component; primary algorithm/model imports and exact rational parameter checks, with selected arithmetic lemmas checked in Lean. The event-splice theorem below has a written proof and finite interface tests, not a complete mechanized proof. Independent import/adapter review remains required. This component neither admits SOURCE nor supplies successful physical restoration, current evidence, permissible access, resource affordability or the complete AC guarantee.

The obligation is to supply recurring bounded attempt windows for a finite set of local maintenance tasks, from uncertain offsets and arbitrary bounded protocol state, while relevant programmable suppliers can change over time. A task window is different from a successful repair. The represented interface retains actual event times, origin, finite labels, participant coverage, gaps and operation tails. It omits plant trajectories, message-route internals and code-restoration dynamics; those omitted objects are named suppliers below, not free services.

## 1. Choice and import boundary

Use a deterministic constructed pulser, a finite synchronous counter, and a timed message-round adapter. Run the local preparation/exchange operations in the resulting task windows. The stronger scheduling relation resolves the demonstrated split-lease obstruction without requiring the old common-phase bit-copy substrate.

[✓] Lenzen–Rybicki, [arXiv1705.06173v4](https://arxiv.org/pdf/1705.06173), §§2–6, Theorems1–3, Tables2–4, Corollaries4–7 and Lemmas20/23: the inspected deterministic construction tolerates n>3f and bounded drift, starting with arbitrary protocol/timer state. Its fixed-set theorem assumes prescribed execution outside the fault set, sender-identified bounded-delay communication, and its specified relative-timer semantics. The source implements finite state machines with finite message alphabets and bounded timers. Runtime clock offsets are unused. The exact rational instantiation below avoids interpreting an asymptotic stabilization bound as a deadline. The full published proof is imported, not reconstructed here.

[✓] Lenzen–Rybicki–Suomela, [Efficient Counting with Optimal Resilience](https://jukkasuomela.fi/doc/efficient-counting.pdf), §3, §§4.2–4.4 and Theorem1: the inspected recursive deterministic c-counter tolerates n>3f, starts in arbitrary finite state, and eventually increments its shared output modulo c every synchronous round. The implementation is the finite transition construction in those sections, including the modified phase-king instructions, rather than an assumed correct counter. The explicit round bound below is extracted from the proof. No randomized sampling variant is used; hence there is no per-round failure probability to hide over an infinite horizon.

[✓] Lamport–Shostak–Pease, [The Byzantine Generals Problem](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/The-Byzantine-Generals-Problem.pdf), §3, OM(m) and Theorem1: n parallel OM(f) broadcasts followed by majority of their agreed vector give binary consensus in f+1 synchronous rounds for n>3f. A correct origin's entry equals its input, so uniform correct inputs determine that majority. The Lenzen–Rybicki Theorem5 silent transformation adds two rounds. This deliberately simple finite consensus instantiation is communication-expensive; it is not the communication-optimal phase-king choice used to obtain the headline asymptotic bound.

No lifetime-clean leader is introduced. A designated leader occurs only in a zero-fault recursive block. At a higher level the construction tolerates an entire bad child block; an actually coherent interval must justify the fault partition used by that level. The external supplier must establish nominal code and parameters for the replicas counted as nominal. Altered code does not recover when direct intrusion ends.

The earlier Daliot–Dolev pulse manuscript [cs/0608092v2](https://arxiv.org/pdf/cs/0608092) was also checked: Corollary3.14 states six-cycle recovery, but §3 omits nonzero drift factors from constants/equations/proofs. It is not used to obtain this component's numerical nonzero-drift deadline. Event-local agreement alone also lacks a common task cursor and ordering across different Generals. These are specific reasons for the selected import, not general impossibility claims.

## 2. Explicit finite parameter certificate

Normalize nominal clock rates to [1,theta] and choose theta=1000001/1000000 and phi=1001/1000. This is a positive one-part-per-million drift envelope; delay jitter remains in [0,d]. The parameter checker supports arbitrary positive rational d and requested period P when its inequalities pass. The record checks n=3f+1 for f=1,2,3,4 at P=10^6(f+1)d. Failure of this conservative certificate is not impossibility for that parameter setting. A smaller trial P=10^5(f+1)d fails the advertised phi ratio at f=1; the larger trial 10^9(f+1)d passes but is needlessly slower and was discarded.

The complete executable arithmetic is `pulser_certificate` in [timing_model.py](timing_model.py). At each nonzero-fault recursive node, split n into floor(n/2),ceil(n/2), and f into floor((f-1)/2),floor(f/2). Instantiate the published main/auxiliary/voter/validator machines, with silent consensus length R=f+3. Let sigma=2d and rho=4 theta d. Set X=theta(P+2d), Tactive=6X, T1=3 theta d, Tlisten=(theta-1)T1+3 theta d, and take tau to be the exact maximum in Table3(10). For the initialized simulation pulser use p0=theta(tau+d), p1=theta((1-1/theta)p0+tau), p2=100 theta d, and p3=theta((1-1/theta)p2+2d). The intentionally enlarged recurrent gap permits message processing before the next simulated round.

An explicit safe simulation bound after the final initialization offset is

\[
S_R=p_0+p_1+3d+(R+1)(p_2+p_3+5d).
\]

Indeed the first pulse cluster completes by tau+p0+p1+3d by Lemma2; each further cluster begins within p2+p3+3d by Lemma3. The extra full gap covers the last guarded read/compute. Set Tconsensus=theta(tau+S_R) and Twait=X+Tconsensus. The checker verifies every algebraic constraint of Tables2/3, a bound (X+Tconsensus)/theta+2d <= phi P, and the simulation round margins. Using a conservative upper bound for simulation time is deliberate; it is not a claim that its worst case is attained.

Set Psi=10X and check Psi>Tactive+rho+Tconsensus+2d. For the resynchronizer set x=Psi/(2 theta phi/25), beta=3Psi, Tcool=16 theta beta, and child advertised periods x and 31x/25. Set the other timeouts exactly as Table4(15)–(20), and check (23)–(32) for both children and j=0,1,2,3. Recursively instantiate the children at those requested periods. A zero-fault child uses a leader timeout theta(P+d); bounded initial timeout plus channel drainage gives the conservative stabilization bound theta(P+d)+2d, and its advertised period interval is [P,phi P].

If child stabilization bounds are H0,H1 and their advertised maxima are U0,U1, the explicit recurrence is

\[
T^*=\max(H_0+2U_0,H_1+2U_1)+T_{cool}+\sigma+2d+\rho,
\]
\[
H_B=T^*+\max(U_0,U_1)+\rho+2(T_{vote}+d)+\Psi+11\beta,
\qquad H_P=H_B+T_{active}+\rho+T_{consensus}+2d.
\]

Table4(22) supplies T*. Lemma20 bounds the first correct-block event by T*+max(Uh)+rho; Lemma23's I1(11) adds 2(Tvote+d)+Psi+11beta. Corollaries4–6 then supply the main-machine term. Thus no unknown O-constant occurs in HP. The counter bound uses tau_c=3(f+2), c1=6 tau_c and

\[
N(0)=1,\qquad N(f)=\max(N(\lfloor(f-1)/2\rfloor),N(\lfloor f/2\rfloor))+31\tau_c+4.
\]

Counter Lemma6 spends at most 2+2c1 rounds after its children stabilize; Lemma8 places the good interval before another 3c1 rounds; the tau_c phase-king interval completes alignment. The extra two rounds are slack. In particular N(2)=660. These are bounds for the published transition systems; the Python file evaluates their certificates and does not implement those transition systems.

For n=7,f=2,d=1,P=3000000, the conservative pulser stabilization ceiling is 675520496107 time units. Its advertised maximum gap is 3003000. These large costs are an adverse design finding: the known construction discharges finite timing in this envelope, but its present instantiation must not be called affordable or fast. Choosing another checked consensus implementation or tightening the inequalities is a live optimization; an uninstantiated better constant is not used in the source theorem.

## 3. Timed round adapter, storage and actual work

At a local pulse, snapshot the counter state and clear the finite incoming-round slots. Send the snapshot after local offset S; compute the counter transition after local offset R. One origin contributes one bounded record; arbitrary repetitions do not allocate new records. Missing or malformed records are replaced by a fixed default. Retain local computation cost in the invocation bound J or in the source's event-delay refinement, consistently.

For rate interval [a,b], pulse skew sigma, and nominal end-to-end packet residence delta, the following sufficient conditions separate rounds:

\[
S/b>\sigma,\quad R/b>\sigma+S/a+2J+\delta,
\]
\[
P^->\sigma+S/a+2J+\delta,\quad P^-+S/b>\sigma+R/a+J,\quad P^->R/a+J.
\]

The first ensures all nominal receivers clear before current sends. The second delivers current records before computation. The third drains preceding nominal records before clearing; the fourth excludes following-round records from the current read. The fifth completes the local transition before its next snapshot. Hence every counter transition receives the same nominal previous-round vector that the synchronous theorem requires, with arbitrary entries only at the covered faulty origins. No absolute timestamp is used. After HP, allow three additional pulse gaps to clear pre-stabilization records, align the snapshot/compute pipeline and attach the converged counter value to the following pulse. A static composed bound is H=HP+(N(f)+3)Pplus+R/a+J. The record's n=7 numerical case uses the still larger last term20.

For the internal consensus simulator, the same discipline can use S=4 theta d, R=10 theta d and the p2,p3 gaps above. The import assumes the paper's event semantics with nominal computation included in d; application-level invocation jitter is separately admitted by the displayed adapter. Merely adding J to d does not prove that an independently delayed timer interrupt realizes the imported state machine. That mapping is a source obligation.

All message payloads are bounded: OM paths have length at most f+1 over n fixed identifiers, there are finitely many paths/rounds, and only bits, defaults and bounded labels are stored. For example n^(f+3)(ceil(log2 n)+1) bits per origin per simulated consensus round is a deliberately generous finite payload allowance. Actual serialization, relay replication, parser work and queue service must be charged before selecting d. The virtual-link supplier must maintain its bound under Byzantine flooding, including finite rejection work and appropriate isolation/reservations; a shared unbounded FIFO does not meet it. The complete virtual graph is an imported interface, not a free physical complete graph. Maintenance reach remains separately local.

The parameter tree has finitely many rational timeout thresholds. Their common denominator defines a finite rational quantum q; the largest threshold/q is a finite integer, and the record reports its bit width. This removes unbounded digital timestamps and rounding of the chosen constants. It does not prove a hardware quantization theorem: the imported timers measure relative elapsed local time with the exact stated reset/expiration semantics. A continuously phased oscillator may have a bounded physical phase variable, but storing its phase with arbitrary real precision is not licensed as digital memory. A quantized implementation that resets only on the next tick, or adds expiration jitter, must supply a simulation preserving the inequalities with those errors. That adapter remains explicit rather than being hidden in the word finite. Packet clocks, source variables and the physical plant need not have finite cardinality; the guaranteed digital control/storage representation is finite.

## 4. Event-splice theorem for continuing changes of suppliers

This section proves an interface-level transport, conditional on the imported static algorithm and its source adapter. Its source condition concerns actual execution histories, not a detector available to a participant.

Let a static coherent chart consist of a time interval [s,s+H+L], a set G of at least n-f participants, and the source trace on that interval. Every participant in G follows the actual compiled scheduler code, nominal clocks and bounded virtual-link semantics throughout it; arbitrary internal state is permitted at s. The allowed defects outside G include direct control, still-altered code, suspended execution, scheduled restoration/reinitialization and relevant communication-dependency failures. A single whole-interval cover is required. Applying the static theorem by causal restriction/extension gives, on the suffix [s+H,s+H+L], a sequence of actual pulse events for every participant in G, containing every such participant's pulse there, with skew sigma, same finite label and label increment modulo c, and per-participant gaps in [p,P]. Require p>4 sigma.

The premise that each chart has such G is supplied from raw history by the parent renewal/source proof. An instantaneous bound alone is insufficient. A node's arbitrary post-restoration state is admissible at a chart's beginning, but a later reset is a covered deviation. Past credential or signal capabilities remain covered until the actual source removes their relevant effect. This accounting does not waive the duties of an intact executor whose observations were forged.

Assume the chart premise holds on every interval of length W=H+7Q, where Q=P+4 sigma+1. Choose analytical starts s_j=4Qj, giving suffixes [s_j+H,s_j+H+7Q]. These times and cohorts are proof objects only. Consecutive suffixes overlap for 3Q, and their good sets intersect in at least n-2f>0 participants. Choose one actual shared participant a_j. In the overlap, let e_j be its first pulse at or after s_(j+1)+H+sigma. Its gap bound gives

\[
s_{j+1}+H+\sigma\le e_j\le s_{j+1}+H+\sigma+P.
\]

Both whole pulse groups containing that event lie in the overlap. This is the same physical event at the same participant, not merely equal timestamps or a repeated finite label. It identifies the two chart groups and their label. Each chart lists every pulse of a_j, so consecutive event order fixes the integer translation of all group indices across the overlap. No extra or skipped group can be inserted: a purported insertion would contain an additional actual a_j event between consecutive ones. Other possible shared-node anchors give the same translation wherever their full groups overlap. Otherwise one chart would match two distinct groups across a time distance at most 2 sigma, contradicting p>4 sigma.

Splice at these identified groups. Between splice e_(j-1) and splice e_j take chart j's groups. At e_j take the union of the two identified boundary groups. Splices are strictly ordered, with e_(j+1)-e_j at least 4Q-P and at most 4Q+P. There are multiple internal groups between boundaries, so a boundary never requires an unbounded chain of unions. Discard the incomplete first group at the start of the initial suffix. This produces a one-sided infinite sequence of groups after at most H+P+2sigma; it is purely an analytical representation of actual events already generated by the protocol.

An internal group has diameter at most sigma. A boundary union has diameter at most 2sigma because all its events lie within sigma of the shared event. Each group contains at least n-f participants. Let u_k be its earliest event. Within a chart, the earliest-event gap lies in [p-sigma,P+sigma], by comparison with a participant attaining one endpoint. Replacing one boundary's minimum with the union minimum changes that minimum by at most sigma. Therefore every successive global earliest-event gap lies in

\[
p-2\sigma\le u_{k+1}-u_k\le P+2\sigma.
\]

Since p>4sigma, consecutive global groups are temporally disjoint. Labels continue as (z0+k) mod c: they advance inside each chart and agree at each actual splice event. The common integer k is not stored by the implementation. In particular a c-wrap cannot splice different physical events.

Coverage is precise. On an owned segment the theorem covers all pulse events of that segment's chart cohort, and at a splice it covers both boundary cohorts. Participants outside the relevant cohort may emit other events; those events are not silently certified. At least n-f genuine scheduler outputs support each group, but no fixed lifetime-clean participant need exist. The finite trace test uses the stated stride/suffix construction, rotates omitted pairs over seven participants, and inserts an extra arbitrary event at every participant outside all charts that cover it. It has no lifetime-clean participant at this output interface. It checks the claimed interface consequences, not execution of the imported pulser or source code-corruption dynamics.

An actor that continuously resumes nominal behavior at r is handled without a cure label. For an event at t>=r+W, take a separate coherent past chart ending at t and include every participant nominal throughout it, including this actor. Its long stabilized suffix overlaps an atlas chart containing the relevant event by more than a full guarded pulse gap (at a splice, use the preceding chart). The shared actual-event argument fixes the same label translation. Causal extension past t may finish a boundary pulse group for reasoning, but cannot alter the actor's event or local state at t. Thus its current local output has the established phase after W of actual nominal execution, without knowing r or receiving a cure notification. The proof does not infer nominal execution from the waiting time. A still-altered program can remain arbitrary indefinitely.

This theorem glues short suffixes, not one coherent set over the entire M-task cycle. It therefore avoids charging every actor renewed during a long cycle into one permanent fault set. The parent must nevertheless show that the short-window cover remains nonempty under its concurrent attacks, legitimate maintenance and supply interruptions. The written event proof, especially causal maturity and the compiled-state-machine correspondence, needs independent review before being used as a fully discharged source lemma. Lean checks selected splice/gap/label arithmetic, not the entire existence theorem.

There is an explicit admission obstruction at the present conservative constants. If all seven scheduler replicas are forcibly shut down or reinitialized once in a task rotation shorter than W, every one belongs to that interval's deviation cover: its size is7, not at most2. For B=10 and seven tasks at the sample minimum period, the full nominal rotation is210000000, far below W. The script retains this counterexample. Therefore a naive proactive full-cohort reboot schedule cannot use this adapter. A source must instead establish a faster maintained-joining/closure result, avoid resetting nominal scheduler execution during the chosen maintenance, or use a justified slower intervention schedule and recompute sustainable damage capacity. None of these alternatives is supplied by changing the chart labels. This is failure of the sufficient window adapter, not an impossibility for every mobile synchronizer.

## 5. Cyclic attempt allocation and cleanup

Fix finite M>0 tasks and B>=3 pulse phases per task; use c=BM. Decode task=floor(z/B) and phase=z mod B. A task may describe a target, candidate/module and a fixed local operation variant; its index does not assert permissibility. Every cyclic traversal of c labels contains exactly one phase1 start for each task. The checked `task_cycle_hit` supplies the bounded wait to any particular label. With global maximum cluster gap U=P+2sigma and global skew Sg=2sigma, a conservative revisit bound is cU+Sg+J+delta_command. This is independent of requester arrivals. An absent or malicious requester cannot delay advancing the task cursor.

The first phase clears transaction data and drains prior effects. Interior phases attempt the finite elementary operation sequence. The final phase issues release/retreat and stops new task commands. If elementary work takes at most A and actual release plus old command/effect drainage takes F, use a block satisfying

\[
(B-2)(p-2\sigma)>A+F+2S_g+2J+2\delta_{command}.
\]

The quantities A and F must be derived from actual source instructions, packet/chunk counts and physical stroke/force progress, including failed operations. They are not abstract successful-repair timeouts. Ending a task label neither retracts a launched effect nor frees a physical dock. A Byzantine actor can continue exerting its admitted influence after the label changes. Its power is retained in the physical and resource proof.

Finite tags may be reused only after actual tails are bounded. For a nominal one-response-per-request path, stopping old requests at time s eliminates their final responses by s+2delta+J. A wait D with D/b>2delta+J and a receive-slot clear suffices for that tail. Autonomous retransmissions, relays and internal processing queues add their actual tails. An adversary retaining a transcript can retransmit after the tag wraps while respecting channel residence, so a drain is not an anti-replay theorem. Current-origin channel realization or actual removal of old reach remains required. The scheduler's own message slots use the round adapter, and its modulo label never supplies unbounded freshness.

The four-guardian lease-split trace is a strict contrast. Let two requesters use quorum3. At every retry, guardians0/1 first receive A and guardians2/3 first receive B; use fast delay1/4 and slow delay3/4, both below1. Each grants its first request for10 units and then both requesters drain for2. The same allocation repeats forever; every actor is correct and timely, no requester obtains3 grants, and all conflicting-lease safety constraints hold. The cyclic scheduler has no competing request-acquisition stage and therefore removes this particular obstruction. It does not establish universal superiority over all lease protocols.

## 6. Complete warm-up condition and resumption

Self-stabilization does not provide a trustworthy readiness bit. Before stabilization, local pulse/counter labels may be arbitrary. The following full conditional initialization is one admissible interface, not an already supplied source fact. Relative to an analytical time0, enough nominal scheduler replicas and their virtual communication begin within a known bounded start spread S0; code/parameter values are nominal but phases/offsets/protocol state may be arbitrary. Their imported timers and initial packet residence satisfy the declared bounds from then on. Required physical service is maintained by a separately proved startup operating mode throughout [0,S0+H+7Q+A+F]. That mode must remain safe under all pre-stabilization schedule outputs and the admitted simultaneous faults. Invasive task commands are inhibited by actual local protocol state until a relative warm-up duration Omega has elapsed from that actor's genuine local start, with Omega/b>=S0+H+7Q. The inhibit/warm-up state is a characterized initial-family condition; it is not assumed to survive arbitrary code corruption.

This does not give common phase zero: start times differ, timer/counter state is arbitrary, and the pulser constructs their relation. For an actual reconstructed actor, the installation mechanism can initialize a local warm-up state only by writing it as part of the real image. It then waits Omega/b>=W before consuming scheduling output. If interruption or continued changed code prevents those operations, the actor stays in the actual defect cover; no cure alarm is used. Alternatively the parent can prove a startup physical invariant that tolerates arbitrary early scheduling, but merely saying all actors wait is not that proof.

An intact executor with a forged primary frame still owes its full permission duty at every time, including warm-up. Scheduling availability is not knowledge of low load or installed integrity. If the source admits arbitrary activation of the warm-up flag while execution remains intact, the startup proof must cover the resulting early attempt or supply another actual permission argument. This component grants no exemption by changing the executor's fault label.

## 7. Verification and residuals

Run unoptimized Python3.12 `python timing_model.py --check` and Lean4.33.0 on `Timing.lean` from this directory. `--write` regenerates the owned JSON record after reviewed changes. The record binds the Markdown, Lean and Python inputs with normalized-newline SHA256 values. It checks rational import-parameter inequalities for four fault budgets, endpoint timing cases, the finite cyclic decoder, an actual-event chart encoding with changing cohorts, the periodic lease obstruction, and the failure of the window cover under a rapid full-cohort reboot schedule. These tests are first-pass evidence and do not validate the complete published protocol or empirical hardware assumptions. The selected Lean results use only propext, Classical.choice and Quot.sound; no task-specific axiom or admitted proof is used.

Remaining root suppliers are actual code restoration and maintenance downtime accounting; source-derived whole-window covers; flood-resistant current-origin virtual messages with costs; a refinement of physical timers/invocations to the imported alarm/event semantics; startup physical service/inhibition; factive permission/evidence under primary-frame faults; image continuity, successful installation, release and resource bounds. The explicit large startup cost must be tested against those suppliers rather than concealed by asymptotic notation. Needed review is independent checking of the import parameter derivation, simulated consensus timing, and event-splice/maturity proof. No repository acceptance or full-source completion is inferred from these artifacts.
