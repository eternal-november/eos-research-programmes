# Candidate family: processing cells with learned telemetry and physical boundaries

29 October 2026. Prospective design, not an experimental result. This is a candidate for the target gate, not a frozen protocol.

## Plain-language target

A processing line has several stations that must do sustained useful work without overheating one another. Their temperature reports travel through shared electronics. Changing one station's controller can therefore hurt another in two different ways: it changes heat production, and it can delay the other station's measurements. We want to learn which stations actually share these effects, how long the effects last, and what evidence connects their measurements to the physical limits. Then a new controller can be checked against that learned boundary without rebuilding the proof of the entire line.

This is not a sensor-to-braking chain. Heat, telemetry traffic, work scheduling, and fallback reserves interact in feedback over repeated missions. It is also not claimed to be a validated thermal plant: the first model is an expressly synthetic process-cell class with supplied physical contracts.

## What is supplied, and what is actually discovered

Supplied:

* Calibrated physical quantities and units: each tagged channel refers to a specified physical zone; command meaning, physical capacity, service-work semantics, and an independent commissioning reference readout are explicit premises.
* A permitted stable linear dynamical class (or finite-memory transport-load subclass), parameter bounds, bounded disturbance envelope, maximum scope and memory/queue sizes, and a finite candidate grid or an explicit separation/slack hypothesis. Generic RC dynamics are not exactly finite-memory; retain physical state or include a proved residual-tail bound.
* A finite family of causal telemetry transducers: bounded FIFO or round-robin servers, packet sequence identifiers, request/capture/delivery events, possible capture-at-request versus capture-at-service rules, and bounded averaging windows. Supplied event semantics are not inferred from numerical coincidence.
* A declared statistical noise model supporting simultaneous/adaptive-valid prediction or calibration intervals. Do not infer independence of arbitrary noise sources from a finite sample. Shared calibration variables and allowed sharing patterns belong to the candidate class; unresolved relations remain joint.
* A physically justified low-load commissioning envelope and fallback authority, including the maximum detection/actuation delay. No safe experiment is assumed merely because commands are small.

Discovered from actual low-load interventions and records:

* Nonzero physical input/output scopes, relevant lags or recursive observer state, and their uncertainty.
* Which requests contend for a telemetry server, how past requests affect current report age/content, and which averaging/capture possibilities remain.
* Which correlations or persistent calibration relations must cross a proposed component boundary. The inference target is a sufficient predictive interface, not necessarily unique physical wiring.
* A sufficient history/state summary and an interface preserving the joint physical/protocol/statistical relation. Two indistinguishable internal decompositions must remain equivalent possibilities, not be arbitrarily resolved.

The independent reference is an honest additional measurement capability with paid time/occupancy and declared accuracy. Without it, physical response and sensor averaging can be observationally confounded; discovering both individually would generally be false. The target may instead certify their composite predictive relation, but must say so.

## Mathematical shape

One permissible physical family is

    x(t+1) = A x(t) + sum_l B_l u(t-l) + w(t),

with stable nonnegative A and bounded persistent unknown coefficients. Jobs require sustained actuator commands, ordered stages, release times and deadlines, not merely isolated test pulses. Safety includes all delayed tails after jobs finish.

A report delivered on channel i is not simply x_i(now). A candidate telemetry transducer produces capture/window metadata and a weighted report of x_i over a past window, plus calibration and random error. Contention depends on request histories at other channels. The shared physical execution has one plant trajectory, one persistent coefficient tuple, one queue state, and one realization of shared calibration/noise. A thermal envelope must be propagated from the actual report window through all commands and cross-couplings up to the actuation time.

The statistical object says which report errors are covered, with what probability/confidence and under what sampling protocol. The timing object says which capture/delivery histories are possible. The dynamics object maps those histories and errors to a current reachable set and a future physical-load envelope. These are different semantic claims. Taking three independent maxima or multiplying three success probabilities is not generally their correct composition.

The interface can expose a joint relation over:

    incoming physical boundary load; outgoing command/load trace;
    request/acknowledgment/capture/delivery events and queue residue;
    observer state/averaging residue; shared parameter/calibration IDs;
    valid operating modes and statistical event/budget IDs.

Its internal dimension must be measured. Calling the entire world-state relation a boundary would technically be sound and scientifically uninteresting.

## Safe causal acquisition

Begin in a certified low-load reachable state, not a free reset. Exercise candidate request subsets while low-load physical excitation and paid reference measurements distinguish report timing/averaging from actual response. Physical pulses distinguish input scopes and lag effects only when the coarse envelope covers every candidate world and their entire tails. Scheduling queries themselves are interventions: a high-rate polling experiment must be checked against the telemetry and fallback guarantees of active cells.

Finite identification requires a genuinely safe distinguishing family, a separation margin exceeding combined reference/report uncertainty, and coverage. State these as limitations; lack of a safe separating probe yields a larger conservative interface or abstention. Statistical inference must be simultaneous or anytime-valid over adaptive choices. Do not run a fixed-sample test repeatedly until an attractive support graph appears.

## The replacement that makes this a composition problem

Replace a local controller with a new workload/polling policy, or replace one telemetry module with a newly calibrated module, while other stations retain their existing controllers and proofs. The new policy can keep the same actuator amplitude bound yet alter timing, sustained dwell, request bursts, and captured windows. Therefore a physical command-bound check alone is not enough.

A valid local replacement check must establish (i) its physical boundary trace contract, (ii) its protocol traffic/timing contract, (iii) preservation or renewal of statistical premises, and (iv) compatibility with the current queue, averaging, observer and physical tail state. The migration cannot erase pending packets or delayed heat. Draining/quiescence, if used, is an explicit paid transition with continued physical protection.

If discovered support proves that station r's requests do not influence group T, its controller replacement need not invalidate T's timing proof. If it DOES share the server, unchanged heat commands do not protect T: the replacement may age T's reports enough to destroy its available safe work margin. Conversely physical couplings may reach a station on an entirely separate telemetry server. Thus the useful boundary is not one supplied partition and is not just a syntactic proof dependency list.

A replacement that changes physical hardware or bus routing cannot inherit an absence-of-coupling fact on faith. It either supplies a checked conformance witness to the learned boundary, or triggers safe reacquisition of affected possibilities. New hardware generation IDs must distinguish old calibration and queue contracts.

## Prospective relevance and refinement witnesses

These are obligations to prove before freezing an experiment, not achieved results.

1. **Same execution information, refinement.** A smaller coherent candidate set gives a no-smaller robust completion set under the same action/observation interface and accounted costs. A smaller representation of the SAME joint behavior changes computational cost, not capability.

2. **Timing-to-physical strictness seed.** Pick an active cell whose fresh-report reachable upper bound is h, whose increased-age uncertainty adds delta>0, and whose mandatory service segment contributes q. Choose h+q <= C < h+delta+q, with a reachable delayed-history witness realizing the larger envelope. A second controller's request burst can create that increased age exactly when the service deadline forbids waiting. Before learning contention scope the coarse model must admit that burst affects the cell; a safely learned noncontention fact permits the work. In the shared-server world the same replacement must be rejected or throttled. The plant trajectory, packet schedule, persistent parameters and deadline witness must be constructed jointly; interval arithmetic alone is not proof of a realizable counterexample.

3. **A richer family is mandatory.** The seed above is only a diagnostic. The main workloads require repeated overlapping multi-stage jobs, several physically coupled zones, different averaging windows, multiple shared servers and online changes. Include cases where memory/averaging distinctions matter, not only discovered static bus membership. At least one accepted replacement must have a different temporal policy, not a renamed controller.

4. **Locality/cost witness.** On N replicated but initially unknown sparse clusters with bounded learned physical/protocol separator size k, a replacement whose checked joint boundary contract is unchanged can reuse the complement's certificates. Count the checked boundary/interface and changed proof size, all support-acquisition cost, and storage. A one-time whole-system discovery cost can be linear in N; do not hide it. Long-range physical propagation, one shared calibration variable, a global bus, or growing conditioned width can destroy this advantage and must be included as negative families.

5. **Stateful necessity.** Produce two histories with identical latest sensor values and static dependency edges but different pending-packet/averaging/delayed-load residue, one replacement-compatible and the other incompatible. This excludes a latest-value static graph as a sufficient assurance interface. It does NOT exclude a strong generic dependency verifier that explicitly retains the same stateful relational information.

## Online validity without magical safety

Changes to declared traffic modes, report-age limits, reference calibration expiry and temperature-regime bounds are monitored at their specified event boundaries. The currently valid certificate must already reserve enough headroom for the worst detection/actuation delay and remaining physical tail. A predicted expiry can trigger fallback before the guarantee lapses. An unannounced violation outside the modeled detection envelope is loss of assurance, not a proof of safe recovery.

Maintain validity of the *joint event*: shared calibration data is not charged once per cell as independent; an unchanged old event can remain usable while a new component obtains a distinct valid event. Replacing one member of a shared calibration relation may invalidate cross-boundary deductions even when each marginal error bar is unchanged.

Fallback and completion are separate: safe throttling or idle can protect cells but miss deadlines. Results must record refused replacements, lost completions, paid reacquisition and safety-envelope exits, not just successful substitutions.

## Strong baselines and claims that should NOT be made

* Coherent whole-system recheck uses exactly the same candidate worlds, records, clocks, correlations and replacement traces. It should match capability. Any claimed speed benefit must include conversion and proof-reuse setup.
* A strong fixed-interface baseline receives a conservative supplied all-possible-neighbor/history contract; allow appropriate fixed local interfaces designed by an expert as an upper-information reference. Do not compare only against a strawman that forgets all history.
* Generic dependency/incremental verification receives the same learned semantic supports and stateful relations when testing incremental-checking novelty. It may match the proposed update work. Then the contribution, if any, is discovery of sound useful semantic supports, not a new invalidation algorithm.
* Dense learned joint model, safe mission rehearsal where applicable, and an oracle with actual physical/protocol structure provide information and acquisition comparisons. A rehearsal of heat commands alone is insufficient when a replacement changes future request policy, but a baseline may rehearse complete admissible joint traces and cache them.
* Sensor/telemetry contract composition and provenance are already established methods (including ScenicProver). This family earns a contribution only if nontrivial boundary/memory discovery and reusable local replacement survive those baselines.

## Gate recommendation

Proceed with theorem and exact witness construction first. Do not yet implement a benchmark or claim that this family passes the gate. Main unresolved items are a concretely safe distinguishing suite for the joint class, a realizable stateful strictness witness, and an interface size/recheck bound not merely assumed by naming a sparse graph. If these cannot be made explicit, report failure rather than inflate the candidate into a result.

## Exact regression fixtures for the gate

These deliberately small fixtures isolate obligations. They are NOT a replacement for the interacting workload family, nor demonstrations of a new algorithm.

### A locally conforming replacement that must be rejected

Use a discrete FIFO telemetry server processing one queued request per slot. Each request captures its tagged zone at service, and delivery is immediate at that slot's end. Controller A and cell B may share this server; actual sharing is not supplied. B requests a fresh report for its mandatory heating stage at slot 2. The old A policy leaves slots 1 and 2 free. A replacement sends a burst of two requests before B's slot-2 request. Even if its average request budget over a four-slot window is unchanged, FIFO order delays B's report beyond its slot-2 decision deadline. A second replacement moves A's two requests after slot 2 and preserves B's deadline; it is temporally different from the old controller and is admissible.

Normalize B's report error to zero **conditional on the calibration event for this regression only**. B's prior report at slot 0 was 4. Before slot 2 its unknown positive disturbance increments lie in [0,1]. Thus with no fresh report its current reachable interval is [4,6]. A one-slot stage adds 3 and the next disturbance adds at most 1; capacity is 9. The stale-report robust bound is 6+3+1=10, so the burst replacement cannot retain the old stage certificate. One coherent compatible world realizes the bound by choosing both intervening increments and the next increment equal to 1. Safe idle instead gives at most 7, so a physical fallback is available although the stage deadline is lost.

If B receives a current report of 4, the identical stage bound is 4+3+1=8<=9. The fresh report is realizable in the world with zero preceding increments. This is a **conditional safe-completion capability witness after observed evidence**, not a claim that every disturbance world can meet the deadline. Do not turn it into a universal positive acquisition/completion theorem. For nonzero calibrated error e, replace the two bounds consistently and choose strict margins.

The exact same burst replacement is harmless to B's timing if discovery has proved that A and B use separate servers. A conservative all-possible-sharing interface must retain the harmful possibility. The distinction is causally testable during safe low-load commissioning by competing requests and tagged delivery times, under a bounded finite server-class assumption. A larger unknown interference class can defeat finite separation and must remain unresolved.

This fixture exposes why an actuator-only or average-request-rate interface is too weak. A generic stateful assume-guarantee verifier with the correct server model will also reject the bad burst; that is a baseline success, not a proposed advantage.

### Static support plus latest value is insufficient

Two permissible report mechanisms have the same physical channel, same static support edge, same latest displayed value 4 and same units. One is an instantaneous current report. The other is a two-sample average with previous/current states 3 and 5. Under a supplied one-step rise bound of 2, both records are legal; the average does not entail current state 4. A next-stage contribution of 3 and next disturbance at most 1 gives upper bounds 8 versus 9. Capacity 8 separates the certificates. Accordingly a learned sufficient interface must retain which averaging alternatives remain and enough window state; merely knowing the sensor's zone and graph neighbor cannot establish the physical conclusion.

Again, the physical averaging meaning is supplied, and the actual mechanism can be separated using a safely varying reference trace only with an explicit margin/error hypothesis. This is a concrete lower-bound witness for memory/content semantics, not a claim that all averaging windows can be inferred cheaply.

### Statistical validity update that is not a Boolean reset

Suppose one commissioning calibration event E_old simultaneously supports several channels with failure probability at most alpha_old. A new telemetry module obtains event E_new with allocated failure probability alpha_new; its error process is permitted to remain correlated with existing channels. During the entire mission the valid union bound is at most alpha_old+alpha_new (plus separately stated operational/physical events), not a product of per-cell successes and not a fresh alpha_old allowance every time an old certificate is rechecked. If the calibration/model permits stronger joint bounds, preserve their actual witness rather than inventing independence.

At a declared calibration expiry, old evidence ceases to justify specified future predictions; it does not remove probability already charged for past operation or retrospectively invalidate an interval on which its premises held. If post-expiry drift is only bounded more coarsely, restore the corresponding old uncertainty/scope possibilities for future use. If no drift envelope is promised, no finite safe post-expiry report bound follows. A replacement with pending packets spanning old/new calibration epochs must retain packet provenance and apply each event to its stated capture window, rather than relabel all received packets with the new certificate.

## Anti-bypass baselines and event ordering

If physical dynamics and all inputs are known tightly enough to predict current state, telemetry may be unnecessary. Include a no-new-telemetry robust predictor using exactly the same dynamics, disturbance bounds and history. The FIFO regression genuinely needs current information because independent disturbance increments remain unresolved; its strict claim is conditional certification after a realizable low report, not guaranteed completion in every initial disturbance world.

Also include a latest-capture-time safety monitor. It can detect an old report and refuse work, so learning contention need not improve safety. The intended gain is certifying a replacement's future report availability before committing to a deadline-constrained task, or correctly interpreting non-instantaneous captures. A timestamp oracle that discloses averaging/capture semantics is a stronger-information baseline, not something to exclude without reason.

For the FIFO fixture, make each slot's order explicit: enqueued requests compete for the slot's service; capture/delivery occur at service completion; the physical work decision then occurs using available reports; physical update follows. Two A requests enqueued before B's slot-2 request, with one serviced in slot 1 and one in slot 2, delay B until slot 3. The old policy and an accepted replacement that enqueues A's burst after B's slot-2 service leave B available for that decision. Physical increments between capture 0 and capture 2 are the two increments used in the stale bound.

## Concrete acquisition subfamily (suggestion coordinated with theory worker)

A deliberately narrow but constructive subclass uses unit-rate bounded FIFO servers, a known deterministic tie rule, and an unknown partition of ports among servers. Empty-queue simultaneous pair requests distinguish shared from separate servers by serial versus simultaneous delivery. There can be O(n^2) such pair tests; count queue drain, safe reference trajectories and physical clock cost. Do not advertise linear discovery without a better certified query design.

A queued request during a known safely varying reference ramp separates capture-at-request from capture-at-service, and a sufficiently separated ramp/window family can distinguish allowed averaging widths. If capture time is directly reported as trustworthy metadata, do not pretend to discover that part indirectly. All distinctions require gaps larger than combined reference/report errors. Physical FIR scope and lag acquisition can use the previous low-amplitude isolated-pulse method, with its known limitations and total tail cost.

The statistical component should actually determine a useful prediction/calibration band, not be a decorative probability label attached to a deterministic hard interval. One option is a supplied finite family of joint error laws with an anytime-valid surviving set. The discovered boundary retains all surviving shared-error couplings. Operational prediction risk and training-set exclusion probability then remain separate. A finite operational error support can simplify exact checking but cannot be inferred merely from the absence of observed tail events.

## A concrete growing subclass and acquisition protocol

This section makes the proposal executable in principle without asserting an experiment has run.

### Growing physical/protocol class

Use n physical zones and n actuator/request ports. Physical response is an unknown nonnegative sparse FIR operator with coefficient grid, at most s nonzero input-lag terms per zone, and lag ceiling L. It models a synthetic finite transport-load plant; all-off flushing, low pulses, and tails use the previously established conservative commissioning envelope. Add an unresolved contemporaneous bounded disturbance/current-state component observed only through telemetry/reference, so a known command operator does not make reports redundant. The disturbance law or worst-case envelope and any persistence must be explicit.

The telemetry ports have an unknown partition into unit-rate FIFO servers of size at most b. Maximum queue length Q and overflow semantics are supplied. The deterministic tie rule is supplied. Each channel has an unknown capture rule from {request, service} and unknown averaging width in {1,...,W}. The allowed meaning of averaging and tagged source zone are supplied. Protocol memory is its pending request queue and pending capture/window payloads; one scalar age is not enough for averaged or request-captured packets. Actual server groups, widths and capture rules are not named in universe factor labels.

A discovered implementation interface stores the relevant FIR command suffixes, finite queue state, pending captured payload relations, averaging sufficient statistics/residue, observer reachable-state bounds, and retained shared uncertainty factors. Global dependency through repeated feedback is possible. A local replacement theorem requires unchanged checked boundary trace/envelope (or a declared bounded horizon cone), not merely sparse immediate neighbors.

### Statistical class with a real acceptance effect

For a tractable initial statistical subclass, the error of a synchronized acquisition frame is a finite-valued signed residual. Channels are partitioned into unknown shared-error blocks of size at most b_e. Within a block they share a Bernoulli draw; different blocks are independent **as an explicit model-class premise**. Frames are independent conditional on the declared stationary mode. The dangerous under-reading sign has probability p in a finite separated grid bounded away from 0 and 1. Amplitudes are from a separated finite grid. Reference error is bounded sufficiently tightly to decode residual signs/amplitudes during commissioning. General correlated noise is outside this first subclass; unresolved candidates remain joint rather than defaulting to independence.

This model genuinely changes statistical risk: if m eligible channels share one dangerous-error event, its probability is p; if they belong to m independent blocks, the probability that at least one under-reads is 1-(1-p)^m. For example p=.02 and m=5 gives .02 versus approximately .0961. A preallocated operational budget between those values can permit the joint workload under the first relation but not the second. The physical proof must ensure safety outside the declared bad-error event; this is a probabilistic guarantee, not zero-risk hard safety. A hard-envelope fallback remains available but can lose service deadlines. If the project requires deterministic zero-risk completion, this statistical distinction cannot buy that stronger guarantee and the claim must change.

Do not apply those probabilities naively after adaptively selecting channels from the same noisy frame. Either choose the eligible set predictably before the frame and bound the event over that whole set, or certify the full adaptive policy's joint law. Reusing a queued/cached sample reuses its event ID; it is not a fresh independent draw. Unknown physical state and selection bias must not be silently conditioned away.

### Paid safe learning stages

1. Establish a low-load reachable commissioning state with safe flush and charged elapsed time. Prove that reference sensing, request traffic and all probe tails remain within the coarse physical/fallback envelope.
2. Isolated low-amplitude actuator pulses and reference traces identify grid-separated physical coefficients/scopes/lags, or retain a conservative candidate set if separation fails. Count n(L+1)-scale input exposure, reference costs and return-to-safe-state time; no new claim over the earlier FIR acquisition mechanism.
3. With emptied queues, simultaneous pair requests test FIFO sharing. Separate servers deliver together; a shared server serializes. There are up to n(n-1)/2 pair tests, each with bounded draining time. This is a real quadratic discovery bill. Group results must be consistent with a partition; inconsistent evidence/model violations are reported rather than patched into an arbitrary graph.
4. Under safe nonconstant reference traces, queue requests and distinguish capture rules and averaging widths. A finite separating trace suite exists only if its physically safe range/slope and reference error give a strict separation gap for the allowed transducers. Require that suite explicitly as a class parameter; lack of it leaves an unresolved transducer relation. Do not invent a safe ramp for a plant that cannot produce it.
5. Collect a fixed number N of synchronized reference/residual frames per declared calibration epoch, or use a proper anytime-valid alternative. With p bounded away from 0 and 1, distinct independent blocks have mismatch probability at least q_min>0. For each pair, observing a mismatch rules out exact sharing; no mismatch after N frames can misclassify independence as sharing with probability at most (1-q_min)^N. Union-bound over all pairs and all predeclared epochs. Channel probability estimates use ordinary fixed-sample concentration over independent frames, with a simultaneous allocation across channels/epochs; independence across channels is not needed for that union bound. Choose N prospectively from the allocated identification error and grid separation, not by stopping when a desirable graph appears.
6. Compile the discovered joint interface and prove its frame once for the original composition. Retain original evidence factors and superscopes so expiry can restore eliminated possibilities. Measure interface construction, proof construction and stored witness size. Then offer genuinely changed workload/polling controllers and one telemetry replacement to the same boundary checker.

This is constructive but not claimed cheap. Quadratic protocol/statistical identification can dominate a handful of replacements. Report the number and scale of replacements needed for amortization, if any. The matching incremental baseline may achieve the same recheck savings once given the same discovered semantic frame.

### Finite-horizon validity and risk accounting

Declare a finite mission horizon H and a finite schedule of permitted calibration epochs/replacements, or allocate a summable error budget for an unbounded one. Split training/model-exclusion probability delta from operational dangerous-error allowance epsilon and from any physical-envelope failure allowance eta. On the simultaneous good-identification event, bound the conditional first operational error events using predictable eligible sets and correct persistent/frame IDs. The final safety bound is no better than delta+epsilon+eta unless a separately proved joint argument improves it.

A supplied calibration lease must mean a physical/model guarantee of stationarity or bounded drift until a stated capture time, not just a timer. A replacement starts a new parameter/calibration epoch, and old packets retain their capture epoch. Before a lease expires, the scheduler must have reserved sufficient time/headroom to finish pending physical tails and switch to a hard-envelope safe policy using no expired evidence. If it cannot, the replacement/mission is rejected before commitment. Unexpected changes outside the promised envelope are explicit assurance loss; they are not repaired by deleting a graph node.

Operational risk already incurred remains in the mission ledger after expiry or replacement. Past valid certificates remain valid for their covered intervals. Future conclusions may need widening/restoration of old candidate dependencies, which can bring remote cells into the recheck set. This restoration is a semantic update, not merely a Boolean cascade on the last selected graph.

### Essential timing/statistical bridge: source-frame identity

Index primitive error draws by (shared-source block, acquisition frame), not by channel or packet. Global acquisition-frame semantics and the source's sample-and-hold rule are supplied; which block a channel shares and which frames contribute to its delivered packet are discovered/retained. Two channels from the same block have the same error only when they use the same source frame. A polling replacement that shifts one capture across a frame boundary can turn one shared dangerous event into two independent draws, even if both packets satisfy the same scalar maximum-age bound. Conversely two different packets can reuse the same old draw, so packet counts do not equal independent trials.

Averaging windows may overlap some primitive frames and not others. Their report-error bounds are a pushforward of the joint primitive-source relation through the actual averaging/capture transducer. One cannot apply the instantaneous single-frame p to an averaged report or reissue a budget per delivered packet. The interface therefore retains source-frame incidence (or a proved sufficient quotient), along with outstanding/used event IDs and any needed conditional source information. This is the substantive bridge between the learned timing/content recursion and statistical evidence.

A particularly useful replacement regression preserves maximum report age and per-channel error marginals while changing cross-channel capture-frame alignment. Under a workload that needs a simultaneous joint risk budget, the old certificate can become invalid despite every local check still passing. The generic whole-system baseline must retain the same primitive-frame semantics; an incremental method with those semantics may match the result.
