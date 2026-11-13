# Discovering a compensated tool inside an unfamiliar machine

## Purpose and status

This is one bounded worked application connecting witnessed decomposition, mission-relative observation refinement, and the relative computation/protocol machinery. It is not a new research contract or a generic theorem of autonomous discovery. The principal inference criterion is elementary finite linear algebra. The useful synthesis is an explicit, executable route from safe experiments to a partially identified, context-sensitive interface, including a successful mission and a sharp interruption boundary.

The motivating story is a repair robot in an undocumented workshop. It must complete two machining operations while a replacement connector waits in a fixture, then send that connector down the correct finishing route before the power window closes. The robot can load a desired route bit, but nearby operations can disturb the routing latch through unknown cross-couplings. It cannot inspect the latch during the real job. Learning what happens when the routing station is used alone is therefore insufficient. The discovered object will be a *compensated interface*: a reliable way to use the coupled machine, not a claim that its parts are independent.

The story is illustrative. The finite transition system below is the mathematical object. In particular, safe dummy calibration, physical gating, complete event accounting, the correction actuator and the link between the final bit and the desired route are supplied capabilities and model assumptions.

## 1 The physical family and its trusted boundary

Fix m >= 2. Write F_2^m for binary vectors, addition for bitwise XOR, and c·v for binary dot product. A machine has one fixed but unknown coupling vector c in F_2^m during a declared epoch e. The machine is deterministic given c and its inputs. No probability law on c is assumed.

There is ONE owned station/controller token. All the coupled latch state and operations live under that owner; disjoint labels do not imply independent physical stores. A known scheduler/gate enforces the permitted state transitions. An exclusive physical lease protects the guard and correction in Seal and remains held through Commit and final route capture: no other actor can mutate the latch in that interval. This is not a conclusion learned from successful probes or merely a consequence of writing a sequential client.

A production state has:

- a public epoch e and recorded evidence E from that epoch;
- a target bit x, one fresh pending connector, and a closed physical gate;
- an actual operation history h and its parity vector v = parity(h);
- a multiset R of unconsumed, individually identified useful-work tokens;
- elapsed time and the physical gate's retention/deadline bounds;
- a private routing latch s and the fixed private coupling c.

At load, s := x and v := 0. Each addressed work operation j changes s := s + c_j and v := v + e_j. It consumes a specified work token and produces the corresponding useful-work receipt. Thus throughout the unsealed pending phase,

    s = x + c·v.                                      (INV)

The parity vector is ONLY an interference summary. It is not a summary of useful work, resource consumption, chronology, or token identity. Two executions of an operation may cancel their latch effect while still consuming two tokens and two units of time. Work cannot be repeated without another explicitly supplied token. Operations required by the mission must occur after loading the real connector; doing them in calibration or before load does not count.

A known correction operation can toggle the latch by a chosen bit d. It is used only by the seal transition, after which the owned token becomes Sealed and no more work operation is admissible. Commit consumes Sealed, opens the gate and routes the connector according to s. There is no production readout of s or c. A known safe abort/disposal operation can terminate a pending attempt without opening the production gate; this is mission failure, not successful completion or undo.

Each modeled action has an explicitly specified duration. In the concrete case each action costs one tick, the mission deadline is T=10 and the supplied retention/disposal horizon is H=11. A pending or sealed connector is physically retained until H; Abort is legal only when its one-tick disposal finishes by H. Seal requires t+2<=T and t+2<=H, reserving one tick each for Seal and Commit. Commit requires its finish time t+1<=T,H; its tick includes final physical route capture, with no uncharged delayed tail. Work and Load likewise require their finish time to be within H. A rejected request consumes one tick of controller time but does not change latch, work tokens, evidence or protocol mode. Such ticks consume the same retention budget; a context that exhausts it has no promised safe continuation. Accepted Seal's tick includes its finite row-space validation computation in this bounded implementation. For the finite transition system, crossing H without a completed Commit or Abort enters terminal Expired; no physical safety assertion is made for that state. Both concrete wrapper and abstract protocol expose this same failure. Only finite client traces are claimed. If a platform has a longer capture tail, that duration must be reserved and charged instead. Gate retention, commissioning access, stationarity, exactly accounted work events, and the absence of unmodeled latch mutations are trusted premises. Arbitrary unobserved drift is outside this model and is not detected by the result.

## 2 Experiments are physical protocols, not an oracle

For a desired probe vector q, the robot performs a shielded dummy trial:

1. load a dummy with latch zero and gate closed;
2. invoke each selected operation j with q_j=1, using calibration tokens;
3. read the dummy's collected route bit b;
4. drain/remove the dummy and return to Idle.

The readout is b=c·q by the actual transition invariant. These are real, charged calibration actions. They are not productive-job tokens, and their dummy output cannot replace the required fresh production work. The safe readout and drain are available only in the declared calibration mode, not as a free production sensor.

With unit action durations, this trial costs |q|+3: load, |q| pulses, read and drain. A probe sequence may be adaptive, but each retained row must be tied to the SAME epoch and machine. Record the ordered evidence rows

    E = ((q_1,b_1),...,(q_k,b_k)),   A c = b.

The actual machine witnesses consistency. More generally define V_E={c:Ac=b}; if V_E is empty, the evidence is inconsistent and the interface is not certified. Empty possibility sets must never certify every command by vacuous universal quantification.

The experiments reveal effects of chosen combinations. They need not identify individual couplings or reconstruct a hidden circuit.

## 3 Exact evidence-to-interface criterion

Let L_E be the row span of A. For a production interference vector v, call d a robust correction when

    c·v=d for every c in V_E.                          (KNOW)

Assume V_E is nonempty.

**Proposition 1.** A robust correction exists iff v belongs to L_E. When v=λA, its unique value is d=λb. Different witnesses λ yield the same d.

**Proof.** If v=λA, every consistent c satisfies c·v=λ(Ac)=λb. If λA=λ'A, choose any c_0 in V_E; then (λ+λ')b=(λ+λ')Ac_0=0, proving witness independence. Conversely, if v is not in the row span, finite-dimensional linear algebra gives n in ker A with n·v=1. If c_0 is consistent, so is c_0+n, and their evaluations on v differ. Hence no robust correction exists. This is the usual row-space/null-space duality, not a novelty claim. QED.

The result decides a concrete question: can the robot determine the latch correction needed after THIS actual surrounding execution from the evidence it really collected? It does not ask whether the machine's entire coupling vector is identified.

The evidence determines a linear map δ_E:L_E→F_2. It satisfies δ_E(u+v)=δ_E(u)+δ_E(v). If truthful rows are added in the same epoch, the new map extends the old one. If rows are withdrawn, the certified domain can shrink. Their recorded truth does not turn into physical authority: the evidence and a coefficient witness λ justify a conditional prediction, while the station token and gate enforce access.

A complete target context subspace U can be supported by probing a basis of U. Exactly dim U independent measurements suffice in this protocol to determine all corrections on U; they generally leave m-dim U dimensions of c unidentified. This is about this finite noiseless linear family, not a universal sample-complexity claim.

## 4 The public protocol and why interruptions matter

The production interface accepts E only with a nonempty version space and a valid current epoch. It tracks actual history, tokens and time in addition to v. Its transitions are:

- **Load(x):** Idle→Pending(x,0,R), consume a fresh connector token, set s=x.
- **Work(j,t):** consume the particular remaining work token t at address j, emit its useful-work receipt, update v and s by the transitions above. Gate remains closed.
- **Seal(λ):** allowed only when all mission-required work tokens have been discharged, enough time remains, and λA=v. Toggle s by λb, then return a Sealed token. A zero correction still has the declared seal duration.
- **Commit:** only Sealed→Finished; open the gate and return the route bit.
- **Abort:** safe disposal/closure as supplied by the model, returning failure rather than mission success.

A rejected request is explicitly a rejection, with no physical latch change and the prescribed state/token behavior; it is not silently deleted from the history. A concrete implementation may use validated proof objects or direct row-reduction checks for Seal. A forged or stale proof does not create a token.

A pending prefix can have v outside L_E even when its completed surrounding operation has parity inside L_E. Such a prefix is not authorized to seal. This is the main reason to retain stage-specific state rather than install a permanent statement that a whole batch is 'safe'. Holding a closed gate only buys the time the supplied retention capability actually provides.

**Proposition 2 (production correctness).** Under the stated transition assumptions, every accepted Commit returns x, for every c consistent with the epoch evidence, independently of how a finite admitted client chooses the work order or branches on public inputs.

**Proof.** Induct over the actual production trace to preserve INV, actual token accounting and the closed-gate state. At an accepted Seal, v=λA and Ac=b, so the new latch is x+c·v+λb=x. The Sealed token and the supplied physical exclusive lease prohibit intervening work and any unlogged latch mutation through final capture. Commit therefore returns x. The induction treats actual occurrences, not only an unordered list of operation names. Rejected calls and aborts follow their explicitly defined transitions. QED.

This is accepted-route partial correctness, not a guarantee that every finite client remains physically safe after its retention horizon. It does not turn rejection, an expired hold, omitted work or late completion into success. The following instance separately proves positive mission completion.

## 5 A successful mission with deliberately incomplete identification

Take m=3 and a single calibration vector q=(1,1,0). Its dummy trial costs five units: load, A, B, read and drain. The result b=c_1+c_2 leaves four of the eight machines possible. Neither individual coupling c_1,c_2 nor c_3 is identified.

The real mission requires one fresh A job and one fresh B job AFTER loading the connector. It provides one token for each; the calibration copies do not count. Its full deadline, fixed before calibration, is T=10. The supplied gate retention/disposal horizon is H=11, distinct from the successful-mission deadline T=10. Execute:

    calibration(q) [5];
    Load(x) [1]; Work(A) [1]; Work(B) [1];
    Seal(λ=1) [1]; Commit [1].

The final interference vector is q, so δ_E(q)=b. The connector is routed to x for every hidden machine, and both actual productive jobs are complete at T=10. Either order of the two productive jobs works. A nontrivial discovery has therefore been promoted to a useful interface without identifying all input columns or a hidden mechanism.

For the illustrative observed b=1, the compatible machines are (0,1,0),(0,1,1),(1,0,0),(1,0,1). These are correlated alternatives. Replacing them by independent per-coordinate possibilities admits machines with c_1+c_2=0 and loses the command certificate. No additional physical experiment is needed to recover that lost capability: retaining the original joint row is enough.

An isolated test of the routing station (q=0) distinguishes none of these couplings. In a machine with c_1+c_2=1, simply loading x and then performing the two jobs sends the uncorrected connector to the wrong route. The new observation is relevant because the mission actually requires those interfering jobs before commitment.

**No-learning boundary.** Before any informative probe, the required final parity q has both evaluations 0 and 1 among the eight machines. All production observations before commitment are the same across those machines. With no production readout, no alternate pre-load completion, and only the specified one-shot job tokens, no controller can choose a correction that gives uniform zero-error completion. This compares the exact same mandatory workflow and permissions; adding a production sensor or moving the jobs before Load changes the problem.

**Interrupted mission.** After only A, v=(1,0,0), which is outside span{q}. The evidence permits both values of c_1. Finishing the still-required B job restores v=q and permits Seal and Commit, costing three further units. This is a real repair: it performs the remaining work and consumes time. If B is unavailable or less than three units remain, the specified mission cannot finish under this protocol and budget. At global time 7 (immediately after A), completing B, Seal and Commit finishes at time 10, while Abort finishes at time 8. Safe abort can avoid a bad routing action only when its charged disposal tick finishes by H=11; it cannot count as mission completion. No safe indefinite hold or abort after retention expires is claimed. Repeating A would require an extra work token and would still not satisfy the missing B obligation.

**Lease failure control.** For c=(0,1,0) and q=(1,1,0), the measured correction is b=1. After legitimate A and B and Seal, the latch is x. If an unauthorized B pulse occurs between Seal and route capture, it becomes x+1 and the connector is misrouted. Thus even a correct point-in-time certificate does not replace physical exclusion through the capture tail. This trace is excluded by the supplied lease, not by the experiment.

## 6 Exact abstraction on the certified production language

For fixed truthful epoch evidence E, a fixed finite token pool and a fixed finite horizon, define an abstract production machine that stores the same public x,v,R,history,time and mode, but omits c and s. It predicts accepted Commit's output as x. It implements the same guards, accepted events, rejection behavior, useful-work receipts and costs as the real wrapper.

Relate a real and abstract Pending state when their public state agrees, c∈V_E and s=x+c·v. Relate Sealed states when public state agrees and s=x. Corresponding Idle/Finished/Abort modes have their explicit matching conditions. Every admitted method preserves this relation, with identical public outputs and cost. Thus the deterministic local clauses required for the O5 finite contextual theorem are discharged directly. One owned controller token contains all shared private state; no separated-batch rule is used to pretend the machine has disjoint stores.

It follows that the real wrapped machine may replace this abstract interface in every admitted finite typed production client, including public adaptive choices and repeated use with fresh legal tokens, provided the client signature has no extra hidden-state observations or unmodeled interfering actions. The ideal model does not silently resample c between operations. The proof is pointwise in the same actual c; no prior law is required. If external finite random choices are admitted, their coupling must obey the ordinary O5 hypotheses and preserve correlations in the joint initial state.

The decomposition connection is concrete: the local relations for every work step, evidence row and final correction share ONE coupling witness c and ONE actual occurrence trace. The learned interface forgets that hidden witness only after proving that every retained production observation agrees at each fixed source. It is not enough that some compatible machine can produce the desired output.

The exact O5 instance here is for the fixed-evidence production signature; administrative evidence withdrawal and epoch change below are separate conservative extensions, not silently included among its matched methods.

This exact production abstraction does NOT extend automatically to further calibration probes. Two compatible c values may answer a new q differently. The version-space model is a sound set of alternatives for such discovery operations, not an exact source-fixed decoder that lets each individual machine realize every alternative answer. Calibration and certified production are separate regimes.

## 7 Withdrawal and evidence refinement

The theorem is scoped to an epoch and declared action alphabet. A known reconfiguration is a physical protocol requiring a quiescent Idle station. It consumes/retypes the old station handle, increments the epoch and invalidates old evidence. Recalibration occurs in safe mode before another production mission. Copying an old certificate as ordinary data does not preserve the physical permission to Commit in the new epoch.

A controller may also withdraw a questioned row while the physical machine remains unchanged. The larger version space can invalidate a pending Seal witness. For example withdrawing the only q row in the paired-job case removes the robust correction at q. The controller must obtain new admissible evidence under the actual protocol, restrict its future contexts, or refuse/abort. It cannot pretend the earlier physical work was undone. If there are still sufficient alternative rows, the pending interface can remain usable with a new witness λ. Withdrawal while Sealed invalidates that token: the only modeled continuation is a timely Abort, not Commit or another correction. This conservative policy avoids silently using a correction whose justification has been revoked; a richer revalidation protocol is not modeled. Ordinary accepted Seal/Commit traces therefore rely on unchanged valid evidence through capture. Physical reconfiguration is forbidden outside Idle, including while Sealed.

A contradictory new measurement is evidence of model/epoch/sensor failure; it triggers invalid status, not an empty-version-space proof of safety. No theorem detects an unobserved change that violates stationarity before it causes an effect. This limitation is part of the meaning of the discovered interface.

## 8 Why declared possibilities matter

The base example is deterministic and needs no distribution on c. If the bounded client language includes randomized choices, every declared possibility leading to a work action must still be checked for token, time and Seal eligibility, including a zero-weight declared branch. A probability-only quotient could erase such a branch and therefore lose an all-outcome completion claim. The O7 law-and-possibility semantics can retain it. The guarded wrapper still prevents an accepted wrong Commit on every legal branch; a branch that aborts is not an all-outcome successful mission.

This is an optional preservation check, not a claim that the linear experiment solves general probabilistic learning, adversarial drift, continuous control, physical recovery or concurrent transaction correctness.

## 9 What has and has not been added

- Existing mathematics supplies row-space identification, deterministic simulation/contextual verification, capability-style protocol enforcement, and assumption-sensitive validity.
- The construction supplies an explicit finite application tying the experiment record to a useful compensated interface, the common hidden witness, actual work obligations, timing, and a successful partially identified mission.
- The shared probe relation cannot be replaced by independent marginal possibilities; the post-learning production abstraction cannot be extended to arbitrary new probes.
- The gate, complete action accounting, calibration safety and correction actuator are supplied. A learned certificate is neither a discovered physical capability nor authority to access one.
- The result is an application/synthesis unless a separate prior-art audit establishes more. No large new contract or universal discovery theorem is claimed.
