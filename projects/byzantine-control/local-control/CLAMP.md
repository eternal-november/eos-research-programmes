# Delayed writer cutoff under noisy position readings

Status: derived conditional source fragment for the stage4 proposal in [INSTANCE](INSTANCE.md) at507ed22. The written argument, selected Lean certificates and exact-rational executions concern one closing attempt. They do not admit the full source, construct a recurring renewal server, establish trustworthy code readback, or prove arbitrary-cycle restart. Independent review remains required. No novelty or repository acceptance is claimed.

The target differs materially from the earlier [OPERATIONS](OPERATIONS.md) interface: writers remain connected during small or unrecognized clamp motion. They disconnect only after a detectable-position region and a response-distance reserve. The same raw gross stiction law is reused; ordinary memory cells are still written serially through private leads. The proposed mechanism supplies neither an image-correctness gate nor a primitive close-started truth flag.

## Basis, scope and proof choice

[SOURCES](SOURCES.md) was inspected before this work, together with OPERATIONS and Operations.lean. Its local graph and containment imports do not establish maintenance force or image restoration. The force algebra in Operations.lean already certifies stiction retention, threshold crossing and progress; this component rechecks that file and adds the noisy recognition, cutoff-order and image-preservation obligations. No new literature result is claimed or needed for these elementary inequalities. The proof uses a first-motion obstruction argument and a cutoff-versus-copy-deadline split: either early motion becomes detectable, or writers remain connected long enough for ordinary copying to finish.

Fix a finite set H of actual participating producer banks for this fragment. Each holds an actual mutable reference equal to the intended finite image P, runs the displayed local procedure, has bounded response, and has its own usable seated candidate and private ordinary read/write path. H is a proof parameter unavailable to the local policy, not the current directly acquired set. It includes the actual program, reference, read and physical-capacity conditions consumed below. The root must derive sufficient such banks on the same history; no bank is permanently exempt from acquisition. A participant with an unusable candidate may still help after recognizing closure, but is not credited in this proof's bootstrap force G.

Other actors can repeatedly act through their existing ports and oppose the clamp. Their continuing writes are not fresh acquisition events. Their combined opposing/misdirected clamp effort and mechanical disturbance has absolute bound W. Classifying an effect in W does not discharge an intact executor's prescribed-response duty under a false primary frame; the parent information/permission proof still owes that quantification. Participating bank j has allocated clamp force f_j>0, with G=sum_j f_j. These allocations are residual capacities after all other simultaneously held ports and work; they cannot each reuse a host's full effort budget. Candidate CPU/DMA writers and alternate ingress are already excluded for this fragment. All candidate bodies remain seated and bound to their actual private leads. In a physical adapter, an insertion coordinate at its stop, no nominal opening force and hostile effort below that coordinate's stiction threshold supply passive retention; merely remembering a bay label does not.

The intended conclusion is: a real completed candidate exists when closure first moves, remains correct despite stale expected-value writes, every needed participant has applied persistent closing force before writer cutoff, and q reaches its closed stop within a derived time. These outputs are conditional inputs to subsequent freeze/readback/selection, not useful mission return. The source-wide rule for any consequential contact, world service during this work, energy availability and physical-defect accounting remain separate obligations.

## Raw law and actual observations

The clamp coordinate q lies in [0,Q], starts at0 and obeys the INSTANCE law

\[
\dot q=\operatorname{clip}_{[-v_{\rm act},v_{\rm act}]}\left(c_{\rm act}^{-1}\operatorname{deadzone}_{\theta_{\rm act}}\left(\sum_{j\in H}u_j+w\right)\right),
\quad |w|\le W,\quad 0\le u_j\le F_j,
\]

with outward motion clipped at the endpoints. Design bounds satisfy0<c_act≤c_+, theta_-≤theta_act≤theta_+, and0<v_-≤v_act≤v; v denotes the known upper speed bound used by the policy and geometry. These intervals may be nontrivial: the controller is not recompiled using the hidden true parameters. A settled positive nominal command realizes at least its allocation f_j≤F_j through the declared actuator conversion law; an upper force cap alone would not establish that lower effect. Old signed commands from a previous cycle require the entry treatment below. Assume W≤theta_- and G−W−theta_+>0. Then q is nondecreasing, because total force is never below−theta_act. Hostile effort alone cannot start motion from0. Once every nominal allocated force is applied, motion is at least

\[
\mu=\min\{v_-,(G-W-\theta_+)/c_+\}>0
\]

until Q. For bounded measurable force histories in this nonnegative-motion regime, q(t) is explicitly the minimum of Q and the integral of the nonnegative capped velocity; stalled runs remain nonempty. This is a constitutive gross-force law, blind to cell contents, actor identity and normative permission. A physical defect violating it is not repaired by this proof.

Writer contact is a raw position relation: the private leads remain connected while q<q_c and are disconnected at q≥q_c, where0<q_c<Q. The source performs the value/address write actually requested on each connected lead; disconnected or malformed attempts have nonempty failure outcomes and costs. No ordinary writer can cross to another producer bank's candidate. Both sides of an overlapping host need distinct leads, as INSTANCE specifies. Completed producers stop issuing new writes; any already queued writes from this attempt still contain the reference value for their addressed cell and cannot damage a complete P image.

At a successful position-read invocation at real time t, participant j receives a finite-word value y_j with a physical sampling time s satisfying0≤t−s≤A and |y_j−q(s)|≤epsilon. Epsilon includes measurement and representation error. The local program does not receive s, t, the true q or an integrity flag. J bounds the wait to the required successful invocation/response and subsequent repeated command issue; finite work and read availability must actually realize this bound. Error bounds on the values that happen to arrive do not by themselves supply J. Command delay is at most D through actual application, with arbitrary reordering. For a positive force command, this includes any actuator response/ramp before the lower allocated force is present, not merely emission or receipt. Every admission, rejection, repeated write and eventual application is charged.

Use the conservative current-position lower bound

\[
L_j=y_j-\epsilon-vA.
\]

Choose a positive marker gamma and latch joining only if L_j≥gamma. This guard is sound even when a bounded-age sample predates the return of q to zero: the raw rate gives q(s)≤q(t)+vA, so gamma≤L_j≤q(t). The cheaper guard y_j−epsilon≥gamma is sound only with an additional monotone sample-to-use history or adequate post-reset acquisition. The execution suite exhibits a bounded-rate descending prehistory that defeats that cheaper guard without violating the measurement-error or age bounds.

For every admitted noise and age, the guard succeeds once

\[
q(t)\ge q_d:=\gamma+2\epsilon+2vA.
\]

Indeed q(s)≥q(t)−vA and y_j≥q(s)−epsilon imply L_j≥q(t)−2epsilon−2vA. Choose

\[
\tau=2J+2D,\qquad q_c>q_d+v\tau,\qquad Q>q_c.
\]

The strict distance reserve avoids relying on a simultaneous command/contact ordering at equality. At q_d, every participant latches the closing decision within J. All its previous zero commands arrive within a further D. A repeated closing command issued after those arrivals takes at most another J+D, hence by tau every participant's applied output is persistently f_j. This deliberately conservative bound permits stale zero commands to arrive after newer closing commands. A stronger per-invocation/read contract can reduce the bound, but no such reduction is used here.

## Local procedure and entry boundary

The finite local state is a bounded copy cursor, a completed bit and a joined bit. Entry instructions initialize those fields and clear the per-target outgoing command; they do not repair the actor's code or its maintained reference. The body and its reference are actual physical/mutable state throughout.

On each invocation an unjoined, incomplete producer first tests the noisy join guard. If it succeeds, the producer latches joined, ceases new copy commands and repeatedly issues f_j. Otherwise it reads its current candidate address. It advances only when actual readback establishes the reference value; otherwise it issues an ordinary expected-value write and revisits the address. Completion of the entire address range latches completed and repeatedly issues f_j. A disconnected write does not count as progress. There is no input named close-started and no branch on a good-set label. Both bits stay latched through this closing fragment; the next cycle must clear them through actual execution.

The producer readback condition is stronger than an unqualified bounded-age scalar observation: advancing the cursor must imply that the actual current cell equals P at that address. A current passive read can supply it. A sample acquired after entry can also suffice if the private writer has only ever written the expected value since that sample. An old pre-entry cache returning P while the actual cell is still poisoned cannot. The current implementation uses actual own-cell reads and retains a stale-readback countercase. Constructing their path, timing and physical target binding is still a root adapter.

Entry requires q=0, false joined/completed latches, a reset cursor, and no uncleared previous-cycle nominal force or write commands. This is not a correct-reset primitive. One sufficient partial entry construction holds q at0 with an actual reset interlock while the current nominal program repeatedly executes those local assignments and emits zero per-target commands. Pre-entry commands arrive by D; a clearing command issued after the last such arrival arrives by2D+J. A reset stroke with minimum hold longer than2D+J therefore establishes the command condition, provided the actual program executes and the stated delay/work bounds hold. References and candidate contents remain unchanged. The executable checks this argument with stale initial positive outputs and packets; it also admits a late old closing command as a counterexample when the condition is absent. Returning the whole cyclic apparatus to this reset/interlock position after an interrupted compromise remains open.

## Parameterized construction proof

**First completed-image witness.** Suppose q first leaves0. With all nominal contributions zero, |w|≤W≤theta_-≤theta_act prevents that motion, so some applied nominal closing command is positive. It cannot originate in a legitimate join observation before first motion: the robust guard implies q at its issuance time was at least gamma>0. The entry condition excludes a command or joined latch inherited from a previous attempt. Therefore at least one positive contributor completed its actual private copy first. Address-by-address verified writes and private ownership establish that this physical candidate equals P when the command is issued. Delayed writes from the same attempt also write P at their addresses, so they preserve the completed image. Body retention and absence of a new direct corruption preserve that witness through cutoff and closure.

This proof requires the producer's actual writable/nominal substrate and sound cell readback. The program's completed bit alone is not evidence. A persistently bad sibling sharing its lead can rewrite an earlier checked cell; that is a missing private-port mechanism, not another raw arrival. New direct corruption during or after freezing can invalidate the witness and remains explicitly counted outside the successful-fragment premise.

**Every join is sound.** The lower-bound calculation gamma≤L_j≤q(t) applies independently to every bounded noise signal and every sample age up to A. It does not infer present positive motion from a positive measurement. The clamp's actual monotonicity follows from the force law, not from the observer's label. Once joined or completed, a nominal producer repeats a nonnegative closing command; queued zero commands can delay its applied force but cannot move q backwards.

**All allocated closing effort is applied before cutoff.** If the trajectory reaches q_c at time t_c, continuity and monotonicity imply an earlier crossing of q_d at time t_d. The rate bound gives t_c−t_d≥(q_c−q_d)/v>tau. By t_d+tau, every participating bank's closing output is applied and every preceding zero command has drained. Thus all allocated effort is present strictly before the contact disconnects the writers and persists afterwards. If cutoff is never reached, this statement alone claims no progress; the next argument supplies it.

**Closure does not depend on recognizing an arbitrarily small movement.** While q remains below detectable movement, the private leads are still connected. If an early closer stalls, the others continue actual copying. Let T_P bound the time by which every H producer either completes or joins, provided its writes remain connected until that event. A fixed L-cell program and the stated current-read/write/response bounds yield, conservatively,

\[
T_P=(3L+2)J+(2L+2)D.
\]

For each address, J permits a request, D drains previous requests, J permits a repeat, D delivers it and J permits confirming readback; endpoint slack is included. This is an elementary operation bound, not assumed successful whole-image repair. An actor with unavailable readback or an unwritable candidate does not satisfy this supplier.

If cutoff occurs before T_P, the previous lemma already supplies all applied closing effort before that cutoff. Otherwise all private ports remain available through T_P; every participant has then completed or joined, and all corresponding closing commands settle by T_P+tau. In either case all allocated effort is applied by T_P+tau. The source then advances at least mu until Q, so

\[
T_Q\le T_P+\tau+Q/\mu.
\]

The bound is intentionally conservative and includes no presumed repair-service rate. The mathematical argument quantifies over all admitted bounded noise, sample ages, command reorderings and opposing forces. The numerical executions below sample that class; they do not prove it by enumeration. The proof needs enough H members with usable private candidates for its bootstrap G. Additional correct joiners can improve force after recognition, but a physical-defect budget must not count their unusable candidate as a working copy source without a separate bound.

The response-distance inequality has a specific conclusion. It guarantees all closing outputs are applied before cutoff. If q_c is still detectable but the response reserve is too short, that ordering can fail while closure later succeeds. The comparison suite exhibits this case; failure of the sufficient margin is not called universal impossibility. By contrast, cutting at an undetectably small motion can actually stall the mechanism.

## Checks, source comparisons and retained obligations

The main exact-rational realization uses four nominal producers with force2 each, hostile effort at most2, theta3, c=1 and v_act=v=1. Position error is1/5, age at most2, marker1/2, J=3 and D=2. Thus q_d=49/10, tau=10, q_c=16 and Q=22 satisfy the strict geometry. Another27 histories vary true theta over[3,3.5], c over[1,2] and the actual speed cap over[0.5,1], using one policy, the same geometry and the common lower progress bound mu=0.5. Invocations have different offsets and periods; controllers never read analyst time. The path may deliver old zero commands after later positive commands. Between integer events the mechanical trajectory is integrated linearly, and detector/cutoff crossing times are computed exactly rather than rounded to ticks.

For a three-cell image, T_P=49 and T_Q≤81. The576 main histories cover every binary three-cell reference, four adversarial force profiles, three bounded-noise profiles, three sample-age profiles and two offset assignments. They check first-witness preservation, monotonicity, applied force before and after cutoff, completion and charged work. Of these,168 histories include a producer joining before its own copy completes. Separate1,8,64 and257-cell images exercise the work/latency parameter. The largest source command/copy state is finite for each declared L,J,D; the history used to generate admissible stale sensor samples and the recorded witness identities are checker ghosts, not controller inputs.

The matched early-motion comparison starts with one candidate already correct but still requiring the nominal address scan. A bounded adversarial assist causes q=0.1, then changes to opposition. Cutoff at0.1 disconnects the unfinished producers; bounded negative read error leaves that motion unrecognized, and q stalls at0.1 despite the preserved correct candidate. With the same initial image, force/noise rules and the delayed cutoff16, the other producers execute55 successful private writes during subdetectable motion, add actual closing effort and reach Q at67.9. This is the mechanism's constructive difference, not an asserted readiness event.

| Executed comparison | Supported implication |
|---|---|
| Undetectably early cutoff / same history with delayed cutoff | Early disconnection can destroy progress; continued ordinary copy work restores it in the constructed source. |
| Short response distance | Some forces are unapplied at cutoff, although closure later completes. The ordering guarantee is lost; universal failure does not follow. |
| Positive-noise naive guard | A positive measurement at q=0 can make all producers abandon copying and close without a completed image. |
| Bounded pre-reset sample | The cheaper monotone-history guard can falsely join after reset; the rate-robust guard succeeds on that same bounded-rate history. |
| Undrained old positive command | Closure can start without any current completed candidate. Actual command entry cannot be replaced by an epoch tag. |
| No timely position responses | An early closer can cut unfinished writers and then stall. Error bounds without response availability do not supply joining. |
| Stale code-cell readback | Expected-looking old values can advance every cursor while actual cells remain wrong. Position robustness does not establish code-read factivity. |
| Insufficient force | All copies may complete while the actual stiction law prevents any motion. |
| Retained writer alias | An existing sibling writer destroys the witness without a new acquisition event. Private ownership must be physical. |
| New direct digital corruption after cutoff | Ordinary write exclusion does not remove the raw direct-corruption capability; the successful-fragment premise fails. |

Every offered command application and write attempt, including disconnected old writes, is charged in the executable ledger. The bounded-word work units are not measured CPU instructions or energy. With n participating producers, a conservative per-event bound is2+sum_j F_j+W+n(D+7), including possible batched command deliveries. The implementation specialization has F_j=f_j=2; a variable-force adapter must use the upper force cap for work and the lower allocation for progress. The physical interpretation also needs a finite upper invocation/ingress rate to exclude Zeno work; J's upper waiting bound alone does not supply it. Actual finite-word cost, raw ingress limits, power availability and concurrent neighbor duties must supply the source resource interpretation. There is no free all-history holding or protected scheduling service.

Clamp.lean checks ten selected arithmetic/continuation lemmas; Operations.lean supplies the retained sixteen declarations including the gross-force kernel. The checks are not a mechanization of the entire asynchronous continuous source or of all bytecode semantics. Run `python -B clamp_model.py --check`; `--write` deliberately refreshes the result after review. The record binds these three new sources and the reused Operations.lean, reports axiom dependencies, and rejects optimized Python. The force/request tests continue through their declared horizons after first closure, so continuing old interference remains represented.

The remaining source obligations are consequential: actual current-code/readback relations; bounded successful position responses under shared frontend faults; physical bank-private reach and body custody; code execution/reference support over the same interval; all-path exclusion rather than one named writer; permission and plant service; energy and simultaneous host budgets; and complete cyclic reset/re-entry. A full-age wait after freezing may establish the separate later image-scan relation only with its actual clock/cache/path and target-binding proof. This fragment neither supplies that adapter nor the common-first-bay availability needed by OPERATIONS. The root's recurring H/kappa induction and the full joint AC mission remain open.
