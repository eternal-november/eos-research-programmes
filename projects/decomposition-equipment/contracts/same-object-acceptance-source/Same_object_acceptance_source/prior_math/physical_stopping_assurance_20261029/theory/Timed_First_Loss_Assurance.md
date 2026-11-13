# Timed first-loss assurance from a discovered predictive decomposition

Proof note, 29 October 2026. This is a new bridge obligation, not a claim of a new general runtime-assurance principle. It uses the previous discovered conditional-law certificate and adds a timed physical witness and a single mission-wide first-loss construction.

## Plain-language abstract

A controller can take a useful action because the combination of communication delay and braking response is usually favorable, even when assuming their worst possible combination would prohibit that action. That is a risk-qualified decision, not a hard safety shield: a brake command sent too late cannot recover lost stopping distance. We specify the actual controller schedule, including a local watchdog, and prove that a collision can occur only after a particular, measurable assurance condition first fails, unless the physical calibration assumptions themselves fail. The learned decomposition predicts that entire first-failure event, keeping correlated delays and braking behavior together over the mission. Missing evidence does not disappear: it is harmless only when an independently justified fallback still has enough stopping room. Otherwise it is charged as a failure. The theorem is conditional on a validated physical envelope; logs alone do not validate sensor accuracy, brake authority, or an unobserved obstacle.

## 1. What is inherited, and what is new

`reusable_environment_discovery_20261029/theory/Discovery_and_Reuse.md` supplies, on one training-data confidence event E of probability at least 1-delta, a positive, recursively executable joint predictor Q such that the true conditional readout kernel P obeys

    TV(P(.|h,a), Q(.|h,a)) <= epsilon(h,a)

on a known covered domain. The theorem holds pointwise, simultaneously for policies selected after training. Q has one fixed set of response tables and one coherent source law, with prescribed persistence of unresolved parameters; it is not allowed to choose a different world after each observed action. Its unknown block/scoping/observer discovery is conditional on the stated finite observable-memory structural universe. This new note neither removes that promise nor infers physical calibration from fit.

The older `safety_representation_discovery_20261029/theory/Causal_Evidence_and_Risk_Decomposition.md`, section 3 and its stopping example, already used a physical hazard surrogate and stopping-distance-plus-risk transfer. We do not count those as new. Here the extra construction is a timed, causal controller with a physical inductive witness; a first-loss stopping rule; a precise distinction between safe and unsafe coverage exit; and an exposure-weighted mission-level transfer reusable after controller selection.

### Certified port adapter (required for reuse)

The prior predictor does not automatically certify newly named physical outcomes or a new action protocol. There must be a causal interface adapter: each physical command maps to a permitted source-model action using only currently delivered information; each predicted source record x is mapped to timing/status record y by the SAME known causal transducer T in the true physical model and simulator. Its internal state and any independent randomness are included in the executable schedule. Every termination/missing/failure label used by the proof must be part of the certified output protocol or be the output of this sound adapter; inventing an unobserved crash label does not inherit a learned probability.

**Adapter lemma.** Work on the augmented history containing the source context and adapter state. At an equal augmented history, use the permitted common source action, couple source outputs at error epsilon, and use the same adapter randomness. Equal source outputs give equal adapted outputs. Iteration maps every admissible physical feedback controller to a causal source policy and preserves trajectory-TV bounds by data processing. The exposure sum in Theorem 2 can be computed under Q on these augmented source contexts; the controller need not read them, although its executable coverage gate needs the prescribed information or a separate coverage proof. If one instead wants a pointwise conditional-TV bound indexed only by the coarser physical history, that history must retain a sufficient certified source context (or a separate bound must be proved). A common transducer alone does NOT give that stronger conditional assertion: P and Q can have different posterior mixtures over source contexts after coarsening.

In particular, reusing a source experiment to choose robot speed requires an explicit premise that speed does not alter that source response law except through its declared input map. This premise can be exact in a synthetic embedding. It is not a consequence of a learned source fit and needs new acquisition or physical justification on hardware.

## 2. Timed executable controller

A decision history h contains only records actually delivered before the decision: values, capture timestamps, receipt timestamps, validity/overflow bits, prior issued commands, acknowledgements, and the finite observer registers. No future delay or brake outcome may be read when choosing an action.

A controller program consists of (i) an admission table, (ii) permitted memory updates, (iii) a local monotone watchdog, (iv) a timed brake interface, and (v) the coverage gate and physical interval monitor. An action specifies a speed/acceleration command and a nonrenewable expiry time. Renewal is a new action and requires a new check. At expiry the watchdog commands braking without requiring a network reply. Received acknowledgements do not themselves prove mechanical engagement; engagement lag and braking authority belong to the physical envelope. Missing packets do not reset the watchdog. Scheduling, computation, timestamp error and sensor age are included in the action delay budget.

The predictor, raw-history coverage gate and physical monitor can have different memory requirements. Their combined storage, communication, initialization and worst-case execution time are charged. Added instrumentation must be noninterfering within these budgets, or its altered regime must be included in acquisition and coverage. A predictor that cannot execute within the assumed latency is not an admissible implementation.

## 3. Physical witness contract

Fix a finite mission of at most H decisions, including the complete braking tail after its last admission. Let z be the continuous or discrete physical state and B the event of collision before the end of this mission. The final state must be in an absorbing safe terminal set for the stated mission semantics. For the scalar stationary-obstacle example this means stopped at positive separation, with no admitted future motion; a moving obstacle is not covered by that terminal condition.

For each observable history h, compute an interval/set U(h) of possible physical states. Let G be the event that all independently justified calibration, dynamics, clock and actuator premises hold throughout the mission. Assume

    P_pi(G^c) <= eta_phys

for every controller pi allowed by the implementation contract. This is an external physical premise, not a consequence of fitting Q. If justified only at confidence 1-delta_phys, keep delta_phys separate from eta_phys. A policy-dependent bound may be substituted, but an exploration-only calibration probability cannot silently be reused under a new controller.

A physical backup witness V is a set of physical states together with a locally executable backup program that avoids B and reaches the safe terminal set. Its delay, dynamics and authority bounds are explicit. U(h) subset V is checkable conservatively.

Each executed covered action a has a Boolean, post-outcome certificate F(h,a,y), where y includes recorded timing/status bins sufficient for the witness. F=1 means assurance is lost, NOT that collision necessarily occurs. The following implication must be proved by kinematics/reachability, not by predictive fit:

**Segment witness.** On G, starting at z in the certified physical set U(h), if F(h,a,y)=0, then the entire segment is collision-free, its next state lies in U(hay), and either a subsequent decision is scheduled within the certified segment endpoint or a safe terminal state has been reached. Membership of the next U(hay) in V is NOT required. V is the separate zero-risk exit condition. A risk-qualified segment may leave V during its execution or at its endpoint; that alone is not loss. If the next decision is uncovered while outside V, however, the exit is charged.

This is a retrospective implication: the controller chooses a before y exists. If a collision occurs midway through a segment whose eventual y has F=1, it is charged to that segment's first loss. The data acquisition specification must still define the corresponding failure outcome (including missing/terminated records); silently dropping crashed episodes is invalid. Alternatively use a predeclared failure/cemetery label that all such executions emit.

At a pre-action coverage failure there are exactly two options:

1. **Certified exit:** U(h) subset V and the backup witness applies independently of the unlearned continuation. Execute backup, enter the safe terminal state, charge no statistical risk.
2. **Uncertified exit:** any required reserve/authority/timing premise is absent. Declare assurance loss with cost one. A best-effort brake may still be issued, but does not remove this cost.

On G the true initial state z0 must belong to U(h0). Initial admission requires a certified collision-free U(h0); an initially uncertified condition is itself loss. An implementation may additionally require U(h0) subset V, for example by starting stationary. That extra initial requirement does not force risky subsequent segments to remain in V.

### A sufficient scalar witness, not a learned physics claim

For a stationary boundary, nonnegative initial speed v, upper acceleration a>=0 until braking engages after at most d, and deceleration at least b>0 thereafter, the maximal forward travel is

    R(v,d,a,b) = v*d + a*d^2/2 + (v+a*d)^2/(2*b).

Integration gives the first two terms before engagement; integrating the braking velocity gives the last. If a timestamped range r has absolute error at most e, sensor age at most s and intervening speed at most vbar, current distance is at least r-e-vbar*s. A sufficient full-stop witness is r-e-vbar*s > R(v,d,a,b). A lease of length ell uses d including ell plus the engagement lag, scheduler delay and clock allowance. If using a relative-speed/obstacle-motion variant, derive a different reachability envelope; do not reuse this stationary-boundary formula.

A segment followed by another admission needs a sound endpoint set U and a bound covering the entire segment until that decision, not merely a planned eventual stopping distance. If zero-cost fallback at that next decision is desired, additionally prove U subset V. A one-manoeuvre experiment can instead make the whole action plus stopping tail one segment. Both are legitimate instances of the theorem, but the latter does not establish arbitrary repeated navigation.

## 4. First-loss automaton and physical soundness

Build an absorbing automaton with states `live`, `safe_terminal`, `loss`. Initial violation enters loss. At live h, evaluate the coverage gate before executing the proposed action. Certified exit enters safe_terminal through the backup witness; uncertified exit enters loss. Otherwise execute a, read y, and enter loss if F=1; enter safe_terminal if the segment terminates; otherwise update h and remain live. At the final mission deadline, a missing certified stopping tail counts as loss. Let L be the event of ever entering loss.

**Theorem 1 (physical first-loss reduction).** Under the physical witness contract,

    B subset L union G^c,
    P_pi(B) <= P_pi(L) + eta_phys.

**Proof.** On G and outside L, initialization is in the certified collision-free set U(h0). Induct over live segments. The segment witness proves no collision over each completed segment and establishes membership in the next certified set U; a certified exit is safe by its backup witness. The deadline rule ensures termination cannot leave an uncertified tail. Thus the whole mission is collision-free. Contraposition proves the inclusion. No claim that loss is necessary or sufficient for collision is used. QED.

This proof explicitly explains why a later fallback cannot erase earlier exposure. If reserve is consumed before its trigger, the segment witness must fail or its claimed physical premises are false. There is no permission to replace that case with a zero-cost exit.

## 5. Mission-wide predictive transfer with exposure, not repeated resets

Run the same absorbing automaton and actual controller under Q. Define

    alpha_Q(pi) = Q_pi(L),
    Delta_Q(pi) = E_Qpi[ sum over live covered decisions t epsilon(h_t,a_t) ].

The sum stops at first loss, safe termination or coverage exit; it excludes outputs of certified backup continuations whose safety is proved independently. Each epsilon is the conditional JOINT-output bound, not a sum of independently fitted marginal assurances. With a coarsening adapter, index h in this exposure expression by the augmented source/adapter history as in the adapter lemma; the first-loss automaton and controller can still depend only on their permitted projection. The proof couples augmented histories, not unsupported conditional mixtures on coarse histories.

**Theorem 2 (timed assurance transfer).** On E, for every admissible causal controller pi, including a controller selected from the discovery data,

    P_pi(B) <= min(1, alpha_Q(pi) + min(1,Delta_Q(pi)) + eta_phys).

The outer minimum alone is sufficient; the inner one notes the discrepancy probability cannot exceed one. If only a uniform per-step epsilon is available, Delta_Q <= H epsilon. When a stopped-transcript TV or KL certificate yields a smaller bound gamma, replace min(1,Delta_Q) by the minimum of it and gamma, provided that certificate includes this automaton and its termination rule and both bounds hold on the same declared confidence event. If separately calibrated, intersect their events and charge the union of their failure probabilities; taking a minimum does not make the confidence costs disappear.

**Proof.** Couple controller randomness at equal live histories, so action and gate agree. At each equal covered prefix, maximally couple the joint P and Q output kernels, with mismatch probability at most epsilon(h,a). The probability mass of reaching such a coupled live prefix is no greater than the Q marginal mass of that live prefix. Summing first-mismatch probabilities therefore gives at most Delta_Q. On no mismatch, both automata have the same loss/safe outcome. Coverage failure causes no extra unbounded continuation: it has been deterministically classified as either safe terminal or loss. Hence P_pi(L)<=Q_pi(L)+min(1,Delta_Q). Apply Theorem 1. The pointwise kernel certificate holds simultaneously for every pi on E, so selecting pi after training costs no additional policy union bound. QED.

A statistical statement is therefore: with training confidence at least 1-delta (or 1-delta-delta_phys when calibration is separately statistical), the deployment collision probability is at most the displayed risk bound. Delta, delta and eta_phys have different meanings. A simulation estimate of alpha or Delta requires its own confidence allocation; exact computation does not.

Persistent alternatives must remain persistent. For a family Q_theta, require the bound for every fixed theta and take the supremum. Computing an adversarial row-switching dynamic program may yield a sound relaxation but is not an exact value for that family. Do not condition each new admission on a fresh unconditional certificate or reset its risk budget for free.

## 6. Positive controller synthesis and checkable witnesses

For a finite executable observer/controller state space, search for a policy and nonnegative potential r on live histories/states satisfying r<=1, r(loss)=1, r(safe_terminal)=0 and

    r(h) >= sum_y Q(y|h,a) r(hay)

for every action actually enabled by that policy. At exits use the corresponding exact terminal value. With a finite horizon include remaining time in the state. Backward induction yields alpha_Q<=r(h0); conversely the exact risk-to-go is a feasible potential. A finite-memory state is allowed only when its update and relevant conditional law are recursively valid; assigning the same potential to incompatible histories is not automatically valid. Enforce this inequality for every persistent candidate Q_theta to get a sufficient robust certificate. It can be conservative because one potential may work harder than separate fixed-theta potentials.

With a coarsening adapter, these proof potentials may live on the augmented source state or full finite source history and be evaluated offline. That does NOT authorize the deployed controller to read that state. Its action table must be constant on histories with the same permitted controller observation and memory; otherwise synthesis has secretly given it extra information. A smaller physical-state potential needs its own sufficient-state/inequality justification.

Similarly a nonnegative exposure potential e with terminal zero and

    e(h) >= epsilon(h,a) + sum_y Q(y|h,a)e(hay)

bounds Delta_Q by e(h0). A finite rational policy/table with these inequalities, its timed schedule, the gate and physical segment witnesses is a checkable controller certificate. Verifying the inequalities is finite; finding a small state representation, source realization or policy can be difficult, and certificate size can be large.

The objective should explicitly include useful behavior, e.g. maximize certified progress/speed subject to r(h0)+e(h0)+eta_phys<=rho. Compare against the controller admitting only actions with segment witnesses for every admitted delay/brake outcome. If the learned distribution admits no additional useful action at the same risk budget, this experiment demonstrates assurance plumbing, not a benefit from decomposition discovery.

### Corollary: exact conditional support can certify zero model-side risk

Suppose a separate response-identification event E_response of probability at least 1-delta_response establishes the exact conditional response m(x,a) throughout the deployment domain, with a correctly initialized and recursively updated observer. Suppose also that the declared physical/source model class guarantees a residual support S, independently of empirical frequencies. In the previous additive specialization this is the structural premise Y=m(x,a)+Z with Z in {−1,+1}^n. Let the calibrated adapter map every such source output to its physical segment outcome.

If the synthesized controller admits only actions for which the segment witness succeeds for EVERY z in S at the current exact observer state, and every possible coverage exit either has a certified backup or is excluded by a proved domain invariant, then on E_response no first-loss event is possible. Consequently

    P_pi(B) <= eta_phys.

The certificate has confidence 1-delta_response, or 1-delta_response-delta_phys with separately statistical physical calibration. There is NO empirical-source TV penalty: no source-probability estimate is used in this support proof. This does not assert an unconditional probability-zero failure when the model-class or physical-envelope premises are wrong.

Proof: induction on the same physical segment witnesses, using the exact response and promised support at each step. Every possible physical source outcome preserves the successful segment condition, so the first-loss automaton never enters loss. Apply Theorem 1. Adaptive controller selection is allowed when response identification and support containment hold uniformly on the permitted domain.

This can improve certified progress relative to a guardian using only global physical bounds, because the learned recursive response can establish a narrower valid bound in the current context. It is still robust assurance over that context-specific support, not probabilistic risk reduction. Joint source probabilities are irrelevant to this branch; do not credit the learned correlation with its benefit. The gain must instead be demonstrated by two histories or actions with different exact response envelopes that the supplied coarse guardian cannot distinguish. Known residual support is a strong model-class premise; unobserved residual outcomes cannot be declared impossible merely because none occurred in training. Exhaustively checking all support outcomes can be expensive, although a segment depending on a small licensed subset may use its projected support.

## 7. Why decomposition is operationally relevant, and what it does not do

The discovery stage must return unknown temporal scopes, recursively executable summaries, and shared stochastic groups whose joint kernel passes the previous simultaneous tests. For stopping, separate marginal models of delay and braking can agree while joint adverse combinations differ. The same shared outcome must feed both the latency and braking stages of the physical witness. If two local descriptions choose incompatible couplings or recode sources without permitted information, their separate predictions do not compile this controller.

The physical monitor may need only a small function of that joint outcome (for example whether a timing-dependent braking reserve was exceeded), while predicting that function can require history absent from either instantaneous signal. A smaller observer is accepted only when its recursive update and joint conditional law are certified. If the necessary channels were never aligned in acquisition, neither synthesis nor a shared random seed invents the missing evidence: obtain aligned observations or pay the worst-case uncertainty.

This is not discovery of the physical calibration envelope. Sensor errors, actuator limits, obstacle geometry, true braking authority and safe-terminal semantics remain engineering evidence obligations. The new theorem makes their interface to learned discovery explicit rather than solving them by assumption-free inference.

## 8. Counterexamples delimiting the theorem

**Late fallback.** A robot travels at v>0 with range less than v*d+v^2/(2*b). A watchdog brakes after delay d. Even perfect detection at its trigger cannot prevent crossing the boundary under the equality-attaining trajectory. A software command is not a backup witness.

**Marginally identical, physically different coupling.** Delay and weak-brake indicators both have probability p. One law makes them disjoint, another makes them coincide with probability p. Choose reserve so only their joint occurrence defeats stopping. All separate marginals agree, but risk differs by p. A learned joint source or a worst-case coupling bound is indispensable.

**Coverage exit after commitment.** A risky lease is already under way; its nominal output falls outside coverage after reserve has been spent. Assigning the uncovered continuation zero risk because the program now commands stop is unsound. The exit must be loss unless its physical backup witness still applies.

**Hidden calibration failure.** Two worlds emit identical range/readout streams, but one has an unobserved nearer obstacle or failed brake. No transcript prediction certificate distinguishes them. The physical-envelope event G must exclude and quantitatively charge this possibility; no finite-state factorization resolves it.

**Repeated-window misuse.** A one-admission loss probability p does not imply mission loss probability p for K admissions. Independent admissions give 1-(1-p)^K; persistent shared modes can give very different dependence. The single joint first-loss law handles either; resetting the budget does not.

**Universal shield makes learning optional for safety.** If every admitted action is already safe under every possible physical outcome and backup always applies, alpha_Q=0 independently of Q. Learning may improve performance or avoid conservative rejection, but cannot be credited with establishing the already-unconditional safety fact.

## Status

Theorems 1 and 2 are proved here at the mathematical contract level. The physical scalar bound is a sufficient analytic instantiation. No physical hardware, sensor calibration or braking guarantee has been validated, and this note is not Lean-verified. The exact-rational checker `theory/checks/check_first_loss_transfer.py` passed 15,625 history-dependent kernel pairs with safe and unsafe coverage exits, checking the exposure bound; this is a finite consistency test, not the proof. Full empirical usefulness requires an independently run controller example showing a certified progress improvement, an actual timing budget, and properly accounted data uncertainty. The original categorical contract is not discharged by this bridge.
