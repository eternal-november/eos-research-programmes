# Byzantine Control Research Handoff

## Mission and completion standard

Develop a theory of Byzantine control: characterize, construct, and verify distributed policies that preserve specified invariants and provide required service when some participants can deviate arbitrarily within their actual capabilities. Recover precisely stated Byzantine fault tolerance results as special cases. Extend the theory to imperfect and witnessed sensing, heterogeneous actuation, changing capabilities, and institutional constraints through explicit replacement obligations. Mathematical unification serves construction, proof transfer, and error detection.

Execute this as one sustained autonomous research session, continuing through research, formal work, adversarial checking, and artifact assembly. The deliverable is a coherent research increment with every workstream below accounted for. A workstream can close with a checked result, verified import, construction, counterexample, or a precisely narrowed residual. Completion of the session does not imply completion of the general theory. Do not stop after a plan, bibliography, vocabulary survey, or collection of disconnected definitions.

This is a self-contained research specification. Read [EXECUTION.md](EXECUTION.md) for the explicit authorization to use subagents, the required delegated prior-art assessment, safe worktree and Git ownership, and the orchestration contract. The other companion files are [Foundations.lean](Foundations.lean), [verify.ps1](verify.ps1), and [VERIFICATION.md](VERIFICATION.md); they supply elementary checked results and their trust boundaries. Primary literature is part of the investigation. The substantive model and theorem targets below are proposals; their appearance here grants neither mathematical truth nor institutional acceptance. The initial maturity is `design`, with several `solve` obligations inside it.

Subagents are explicitly authorized for this task. Delegate initial related-work checking and use further bounded delegation where it improves the research; follow [EXECUTION.md](EXECUTION.md) rather than treating earlier user-level no-delegation defaults or an unavailable generic orchestration skill as a prohibition. Within the isolated research workspace, choose proof methods, refine candidate definitions, build executable models, investigate primary sources, and revise failed approaches without requesting routine approval. Preserve the target, changed guarantees, live alternatives, and residual obligations. Repository acceptance remains a human decision. Commit only the session's own coherent changes, with the result status and material meaning changes in the commit message. Preserve unrelated uncommitted work and avoid personal attribution and routine authoring history in the research artifacts.

The governing requirement is distributed realizability of the specified behavior under an explicit environment and fault model. A large winning region computed by a controller with unavailable information is a failed result. A safe shutdown that violates the specified service floor is a failed mission. A formally checked theorem whose assumptions exclude the intended attack is a conditional result whose limitation must remain visible. Prefer a smaller proved statement with an operative mechanism over a stronger statement purchased by hidden premises.

## What generalization must preserve

Fix a context index \(\theta\) containing the system boundary, initial conditions, specification, observation architecture, time model, scheduling assumptions, fault family, adversarial information, cryptographic idealizations, and available control mechanisms. Changing any load-bearing component creates a new problem instance. Retain the old and new indices wherever a comparison consumes them.

For fixed dynamics, controller interfaces, information, and objective, enlarging the admissible environment set weakens the controller's guarantee:

\[
\mathcal E_0\subseteq\mathcal E_1
\quad\Longrightarrow\quad
\operatorname{Win}(\mathcal E_1)\subseteq\operatorname{Win}(\mathcal E_0).
\]

This is the universal-quantifier argument checked as `winning_antitone`. It is not a claim about systems whose mechanisms change at the same time. Generalization therefore requires an explicit exchange: a removed assumption creates an obligation that a refined mechanism, a new observation, a justified residual assumption, or an explicitly changed guarantee must discharge.

For each proposed extension, exhibit the base guarantee, the newly admitted behaviors, a failure witness for the base mechanism if one exists, the proposed replacement, its residual premises, and a translation back to the base behavior where recovery is claimed. Distinguish an enlarged scenario class from implementation refinement: the former admits more environments; the latter usually restricts an implementation's behavior relative to a specification. There is no unique inverse of an abstraction and no presumption that the extension axes form one linear ladder.

Do not impose an architecture consisting of a ledger followed by actuators. A BFT service may be useful, unnecessary, or insufficient for a particular control obligation. Conversely, preserving an arbitrary invariant is not enough to establish a BFT generalization. Recover the chosen baseline's agreement and validity conditions, with termination or service properties under their own assumptions.

An extension may preserve safety while changing progress, latency, computational realizability, privacy, or accountability. State the comparison mode for each property. A positive safety result does not silently carry those other guarantees.

## Candidate execution semantics

### Reference carrier and deliberate restrictions

Use distributed adversarial execution semantics as a candidate reference carrier. A discrete transition game with local histories is a suitable initial formal fragment because finite countermodels and explicit strategy witnesses are available. The carrier is revisable if it hides a material behavior. It is not an assertion that continuous dynamics, epistemic judgments, institutional validity, or privacy reduce without loss to finite state.

Let \(I\) be a finite actor set. Let \(\Xi\) contain the state needed to generate admissible executions, including protocol histories, physical variables, channel contents, resource state, and fault modes when relevant. A product decomposition is optional; if one is used, give compatibility predicates and cross-component dependencies. Writing separate coordinate update equations does not establish causal independence. An actor may control several roles, and a role may span several components.

For each actor, distinguish an action alphabet \(A_i\), a local-history type \(H_i\), and an observation map from global execution prefixes to \(H_i\). A correct policy has type \(\pi_i:H_i\to A_i\). Histories include the actor's available inputs and own actions. Define clock access, memory, authentication evidence, and message receipt explicitly. The analyst's knowledge of the global state or faulty set is not an input to a local policy.

State-dependent feasibility must be reconciled with local action selection. One option uses fixed command alphabets and includes rejection, ineffectiveness, or failure in the transition semantics. Another requires an issued action to be feasible throughout its information class and proves that requirement. Do not type a strategy as returning \(\Gamma_i(\xi)\) while leaving \(\xi\) hidden and the action's availability unaccounted for.

Start with deterministic local policies and a static, unknown faulty set \(B\in\mathfrak F_\theta\). Give a joint Byzantine strategy space \(\Sigma_{B,\theta}\) with explicit access to compromised histories and allowed communication; collusion need not factor into isolated adversaries. Specify whether the adversary sees correct inputs, random bits, actions, or scheduling decisions, and when. Quantification over arbitrary strategies does not grant future information. Environment strategies include permitted disturbances and scheduling; their admissibility should be defined independently of successful control.

A schematic robust synthesis obligation is

\[
\exists\pi\in\prod_{i\in I}\Pi_i^{\rm local}\;
\forall B\in\mathfrak F_\theta\;
\forall\sigma_B\in\Sigma_{B,\theta}\;
\forall\eta\in\mathcal E_\theta\;
\forall\xi_0\in\operatorname{Init}_\theta(B):
\quad\operatorname{Runs}_\theta(\xi_0,\pi_{I\setminus B},\sigma_B,\eta)
\subseteq\llbracket\Phi_{\rm safe}\rrbracket.
\]

The complete policy family is chosen before the faulty set; only its correct components are followed in a run. Require an initially nonempty admissible scenario class and nonblocking execution semantics. If deadlock or termination is possible, evaluate maximal finite executions as well, with an explicit verdict. Empty run sets must not certify successful control.

State a separate progress obligation, normally under a named restriction \(\mathcal E_{\rm live}\subseteq\mathcal E_\theta\). Timing, resource, fairness, and availability premises belong there or in the safety model as appropriate; they are not implied by the word Byzantine. A deadline requires a clock and an elapsed-time semantics, not merely a step count. A service floor might bound delivered work over specified windows. Any permitted degradation or shutdown belongs in the specification before evaluating a policy.

Randomized strategies, computational adversaries, stochastic disturbances, adaptive or mobile corruption, repair, and changing membership are named extensions. For randomness, distinguish sure, almost-sure, high-probability, and expected guarantees; give the measure and adversary access. For corruption changes, specify memory and key leakage, recovery cleanliness, corruption rate, and the meaning of correctness over time. Do not substitute a varying set \(B_t\) into a static proof without rechecking it.

Trace properties are the initial synthesis target. Privacy or noninterference may require judgments over sets of executions. Epistemic statements likewise use an interpreted system of alternative executions. Extend the answer interface when these are activated instead of claiming that every requirement is a predicate on a single instantaneous state.

### Information and strategy uniformity

For execution prefixes \(\rho,\rho'\), define \(\rho\sim_i\rho'\) by equality of local histories. Relative to the declared admissible execution system,

\[
K_i\varphi(\rho)\;\Longleftrightarrow\;
\forall\rho'\sim_i\rho:\varphi(\rho').
\]

Pin the fault, protocol, and initial-state assumptions in that execution system. Knowledge of a signed statement, the statement's truth, and the sender's knowledge are different claims. An authenticated Byzantine message is evidence of an attributed message event under the authentication model. Its content is not a truthful public announcement. Certificate assembly, delivery to one recipient, and dissemination to a quorum are different events.

An information set of physical states may suffice for some state predicates while failing for nested knowledge, future control, fault attribution, or distributed implementation. A proposed information-state quotient must preserve the consumed judgments and admissible continuations. Keep histories or richer information structures until a sufficient compression is proved. Pooled information is an analytic bound unless the protocol can make it available under the actual delays and faults.

The expression \(\bigcap_{B\in\mathfrak F}\operatorname{Win}(B)\) is a necessary condition when \(\operatorname{Win}(B)\) is computed with the faulty set known. It does not establish one policy for an unknown faulty set. The difference is \(\forall B\,\exists\pi_B\) versus \(\exists\pi\,\forall B\); `coalitionwise_is_not_uniform` gives an elementary counterexample. Similarly, independently existing local actions need not form a compatible joint action.

## Checked foundations and limits

The companion Lean file verifies the exact statements described in [VERIFICATION.md](VERIFICATION.md). These foundations are reusable support, not the main research result. Their finite examples isolate failed implications; they deliberately omit physical geometry, communication protocols, and institutional dynamics.

### Whole information classes and continuation

For a one-step observer with information class \(E\) and safe-action relation \(U(x)\), uniform feasibility requires

\[
\exists a\;\forall x\in E:\ a\in U(x).
\]

Pairwise nonempty intersections do not suffice. The sets \(\{a,b\},\{b,c\},\{a,c\}\) intersect pairwise but have no common member (`pairwise_is_not_joint`). Equality of all safe-action sets is stronger than needed for one-step control. Distinct safe-action sets can share a useful action; their mere inequality is not an impossibility witness. `uniform_policy_iff` proves the one-step factorization criterion for a fixed observation map; its classical choice construction supplies existence, not an algorithm or a distributed implementation.

A perfect-information, turn-based, discrete safety benchmark may use

\[
\operatorname{CPre}(Y)=\{x:\exists a_H\;\forall a_B,w:\quad
\varnothing\ne T(x,a_H,a_B,w)\subseteq Y\},\qquad
W=\nu Y.\bigl(S\cap\operatorname{CPre}(Y)\bigr).
\]

Here action sets are nonempty, choices are state-feasible, every permitted successor is adversarial, and the move order gives the controller the information used to choose \(a_H\). State those assumptions when using the fixed point. The displayed predecessor is not a distributed synthesis algorithm. Partial observation requires uniform choices and preservation of a winning information condition under future observations. Liveness requires additional objectives and acceptance conditions; safety closure alone does not supply it.

The checked continuation example has initial alternatives 0 and 1 with identical observations. The only safe first action sends them to 2 and 3, also observationally identical. State 2 needs `left`, state 3 needs `right`; either successful move reaches safe absorbing state 4, and mistakes reach unsafe absorbing state 5. A state-feedback controller keeps all states except 5 safe. One action sends the entire initial information class into that region, yet no observation-based two-step plan is safe. This refutes promotion of a one-step predecessor of a full-information winning set into a partial-observation winning result. It does not refute belief-space methods under their actual sufficiency assumptions.

### Evidence coverage and realized effects

An estimator may supply an envelope \(E_t\) with a proved inclusion \(\xi_t\in E_t\), rather than an exact state estimate. A model supplies an overapproximation \(\operatorname{Post}(E_t,a_t)\) of every permitted realized next state. A certificate establishes \(\operatorname{Post}(E_t,a_t)\subseteq S\). Together these imply next-step safety (`envelope_step`). Initial safety plus preservation at every realized step yields invariance (`invariant_induction`). The recurrence, availability of certified actions, soundness of later envelopes, and implementability remain separate obligations. A receipt or agreed command is not by itself an actuation contract.

Certified safe actions may be conservative. If their set is empty, this proves failure of the certificate method at that information state, not necessarily physical uncontrollability. If the exact uniformly safe set for the admissible indistinguishable states is empty, guaranteed one-step safety is impossible under that action interface. This does not simultaneously prove the existence of a safety-preserving shutdown. Every fallback or probe must be included among modeled actions, with its own timing and service consequences.

### Quorums and threshold gates

For a universe of \(3f+1\) identities, two sets of size at least \(2f+1\) overlap in at least \(f+1\), by \(|Q_1\cap Q_2|=|Q_1|+|Q_2|-|Q_1\cup Q_2|\). If at most \(f\) identities are faulty, the overlap contains a correct identity. The Lean arithmetic result assumes the union-cardinality bound; it does not prove set cardinality facts or protocol behavior.

In a one-shot certificate system where every correct signer signs at most one value per fixed slot, that overlap rules out conflicting certificates for that slot. This short argument assumes unforgeability, distinct signers, an unchanged identity universe, and the stated signing rule. It supplies safety only. Protocols permitting votes in several views need their actual lock and view-change invariants.

A separate single-gate model permits intervention at threshold \(q\), with distinct unforgeable signing shares and correct signers refusing unauthorized requests. Unauthorized safety under \(f\) adversarial signers requires \(f<q\); availability when all correct signers can and will authorize while faulty signers withhold requires \(q\le n-f\). Such a threshold exists exactly when \(n>2f\), checked as `threshold_gate_feasible`. This is not a Byzantine agreement theorem and includes no agreement, transport, actuator-realization, or deadline guarantee. Weighted, overlapping-domain, and dynamic quorums need separate models.

### Evidence refinement and physical facts

Let \(\Omega(e)\) be the nonempty worlds compatible with evidence \(e\), and fix a proposition \(\varphi\), its time index, and the background model. If evidence extension satisfies \(\Omega(e')\subseteq\Omega(e)\), then universal warrant for \(\varphi\) at \(e\) persists at \(e'\). This is `evidence_monotone`. Enlarging the admissible worlds, for example by weakening the fault bound, can instead remove warrant (`more_worlds_weaken_knowledge`).

These facts do not distinguish protocol-constituted facts from physical facts. A sound record of a time-indexed physical event may support persistent warrant; changing the subject from a historical fact to the current state changes the proposition. Model revision, compromised keys, changing authority, and defeasible measurement assumptions are other explicit changes of context. There is no supplied theorem that monotone warrant ends exactly at a protocol/world boundary. Empty compatibility sets must be reported as inconsistency, not exploited to prove everything.

## Research obligations

The following workstreams follow distinct guarantee failures and their consumers. Their compatibility obligations are part of the program. Dependencies guide execution but do not prevent useful literature work or counterexample search elsewhere while a proof is blocked.

### R1 Establish the semantic core and BFT recovery

Instantiate the execution semantics for one precise Byzantine-control fragment. Specify legal policies, fault and environment strategies, initial states, execution existence, safety, and service. Give a constructive instance as a non-vacuity witness. Keep alternative representations live until one supports the required proofs with explicit preservation laws.

Use the one-shot certificate system for a small exact baseline, then Basic HotStuff as a richer protocol target. Basic HotStuff uses prepare, precommit, and commit certificates; correct replicas lock before casting commit votes, and a commit certificate permits decision. Its safety uses voting and lock invariants; its progress depends on additional synchrony conditions. Treat the Basic and chained forms as separate models. This limited protocol summary is checked against Sections 3–4 of the primary paper [S1]; reproduce the actual algorithmic guards in the formal baseline before importing its theorem.

Develop a candidate bridge from valid certificate possession to knowledge of an appropriate conflict-exclusion condition. Distinguish certificate existence from possession. Claims about signers receiving certificates or updating locks are historical event claims. Exact current locks may have advanced. Use an event-indexed lock history plus a proved evolution invariant; do not turn an old certificate into knowledge that every signer currently holds the old lock. The phase progression is not a universal lower bound on epistemic depth.

If \(\operatorname{Final}(x)\) quantifies over all admissible future executions, provide branching-time or continuation semantics. A linear-time formula evaluated on one run does not itself quantify over other continuations. A sufficient knowledge condition implemented by a certificate is not automatically necessary for every correct protocol. To use a knowledge-of-preconditions result, establish its action-locality, system, and necessity assumptions; avoid defining finality over an already safety-restricted run set and then calling the resulting tautology a protocol proof.

Outputs: formal core, a recovered baseline guarantee with its kernel, a checked or narrowed certificate/knowledge bridge, and an explicit boundary between proved safety and remaining progress or protocol obligations. If full HotStuff mechanization is too large, preserve exact source theorem and encoding obligations, verify a bounded model, and label that result accordingly. An abstract quorum lemma is not full HotStuff verification.

### R2 Develop witnessed sensing and decision-relevant inference

Represent separately communication, physical sensing, observation of another sensor's pose or measurement conditions, and observation of the shared target. A witness relation such as \(W(j,i,r)\) is a candidate derived relation, not automatically an extra primitive: exhibit what \(j\)'s local observation determines about actor \(i\)'s interaction with region \(r\). Pin occlusion, calibration, time alignment, measurement noise, shared causes, and adversarial access to the sensing chain.

The reference distinction is between `Reported(i,m)`, `Registered(i,y,t)`, external scene properties, and the reading licensed by a functioning sensor model. Equal external observations can coexist with different internal readings. For example, an intact and a faulty transducer may have the same visible pose, target, and report. `same_external_view_does_not_identify_reading` checks that elementary indistinguishability pattern. Evidence of inconsistency does not identify the faulty party without assumptions excluding alternative sensor, witness, timing, or model failures.

Develop envelopes of world states and fault hypotheses sufficient for control. Exact reconstruction of every physical variable or identification of every faulty actor is not required unless a consumer needs it. Conversely, do not collapse world-state uncertainty and fault-identity uncertainty when they lead to different admissible interventions. A probabilistic posterior is conditional on its model, selection mechanism, and adversarial assumptions; signing reports does not validate the posterior.

Compare three distinct operations: preventing recipient-dependent messages through a channel primitive; detecting inconsistent reports through extra evidence; and reducing the actuator capabilities of an identified party. Reliable local broadcast is a specified channel model, not a property implied by radio hardware. Physical co-observation can improve evidence without removing the sender's ability to lie. A witness graph alone does not establish identifiability or resilience; derive any topology condition jointly with measurement semantics and fault admissibility.

Seek a theorem or counterexample separating state inference, fault detection, attribution, and safe decision. Test how moving sensors, active probing, attestation, or additional witnesses change the information class and the distributed policy. Outputs: a typed observation/witness model, at least one explicit separation, a justified inference or action certificate, and a literature comparison that distinguishes formal guarantees from empirical detectors.

### R3 Characterize capabilities and Byzantine control feasibility

Represent capability through state-dependent action and transition interfaces with time and resource indices. A possible contribution to a transition is different from the ability to force an outcome against other actors. Preserve the distinction between \(\exists u\exists w\) and \(\exists u\forall w\), and between one-step effect and an achievable multi-step policy. A past successful action is evidence of past capability; persistence of that capability needs assumptions. Failure to act does not establish incapacity: refusal, interference, delay, and resource constraints can produce the same observed omission.

Use a joint transition relation to assemble interventions. Independent per-actor reachability relations generally omit interference, shared resources, ordering, and coupled constraints. A direct sum or product of capabilities is justified only when its composition law matches the plant. Actions may change future sensing, communication, actuation, authority, or resource availability. Include those changes in the state or retained history whenever they affect future guarantees.

Specify a fault family over actual actors and components. Role-specific budgets for controllers, sensors, actuators, and enforcers can be useful views, but do not establish independence. Shared vendors, clocks, keys, sites, or operators may create common failure modes; represent justified dependency structure rather than automatically identifying every related component as one indivisible fault domain. Coalition cardinality remains meaningful when paired with the interfaces each coalition controls; heterogeneous influence prevents replacing that analysis by node count alone.

Attempt a characterization of invariant preservation from a named initial region under local information. Separate necessary conditions, sufficient conditions, and an exact characterization. Known-coalition winning regions and centralized full-information policies provide bounds, not distributed implementations. Test whether evidence, communication, and causal constraints can be separated in the chosen fragment; coupling may obstruct that separation.

Outputs: an operational capability semantics, an indistinguishability obstruction, a hostile-actuation obstruction with legal adversarial choices, and a constructive policy for a nontrivial fragment or a precise reason the selected fragment is unrealizable. Describe a result as minimal or weakest only relative to a defined order and a supporting proof.

### R4 Discharge composition and assumption replacement

Target a substantive composition result for the joint estimator–coordination–actuation loop. A candidate theorem has a sound information envelope, a locally implementable coordination rule, a certified nonempty action set, a sound realized-effect relation, and an update that preserves those conditions. Expose joint resource constraints, delays, fault dependencies, and all assumptions used across component boundaries. Avoid circular assume–guarantee reasoning in which each component's guarantee is another component's unproved premise.

The supplied `envelope_step` is the elementary implication at one transition. The research burden is to construct its premises throughout admissible executions and retain service. A monitor detects only within its observation and latency limits; it does not prevent an already completed unsafe action. Monitoring an assumption requires a detection model and a response that remains safe while detection is pending. Some assumptions cannot be fully discharged by monitoring and must remain bounded environmental premises.

For every proposed replacement, identify who supplies the mechanism and what happens if that supplier is faulty. An enforcer, interlock, reference monitor, repair process, or trusted hardware root has a named trust boundary. Terminate the assurance argument explicitly with a verified component, physical restriction, bounded failure assumption, or weaker guarantee. Merely putting the enforcer's name into the model is not an assurance result.

Compare with existing attacked-system separation results [S2] before proposing a new separation theorem. The candidate gap concerns the exact additional burdens of distributed information, dynamic capabilities, timing, and shared adversaries. A failure of one decomposition is a result about that decomposition; it does not prove all modular reasoning impossible.

Outputs: one common-context composition statement, its proof or a minimal coupling counterexample, a constructive non-vacuity instance, and an assumption-replacement ledger. The ledger records the assumption, failure without it, replacement mechanism, verification method, residual trust, and resulting guarantee. Keep it proportional to the actually studied model.

### R5 Minimize coordination while preserving service

Investigate what information or coordination object a control objective actually consumes: a chosen value, common action, compatible local actions, an envelope, a certificate, or a reservation of a shared resource. Formalize the comparison so that a weaker object still realizes the same relevant control obligation. Different physical states can permit the same safe action; exact point-state agreement can therefore be unnecessary. Whether a particular distributed protocol can exploit that fact is an additional theorem.

Nonempty intersection of centralized safe-action sets does not itself supply a distributed selector. Nonempty individual feasible sets do not imply joint feasibility. For permissive controllers, distinguish existence of a safe selector from safety of every allowed combination and from liveness under every allowed scheduling of choices. If a contract allows both actors to choose independently, establish that the resulting product of choices is safe or provide the coordination rule that restricts it.

Maintain a specified service floor throughout the comparison. An adversary may produce plausible but uninformative reports, induce repeated quarantine, or exploit conservative fallback to degrade service without immediately violating safety. State whether the response is preventive control, recovery, bounded degradation, or an honest impossibility. Information that arrives after the last useful intervention time may establish attribution without enabling control.

Outputs: a same-objective coordination comparison with a distributed realization and an explicit service verdict, or an obstruction explaining why the proposed reduction fails. Reduction in communication cost is optional and must retain the timing and evidence semantics of the comparison.

### R6 Model institutional constraints and public evidence

Keep physical or technical ability, permission, obligation, institutional power, and recognized legal or organizational status separate. These are typed relations, not a containment chain. Institutional power describes which acts can validly change a specified institutional state; it need not coincide with permission to exercise that power or with the ability to compel every physical effect. Model credential possession and effective access separately from normative authority where compromise can separate them.

Represent an obligation by its bearer, beneficiary where relevant, triggering condition, required behavior, deadline, and applicable exceptions. Define breach on histories. An `ought implies can` condition is a proposed requirement on an operational assignment of duties, not a logical truth imposed on every normative system. When control and institutional constraints conflict, report the incompatible obligations and conditional alternatives; a safety proof does not establish legitimacy or authorize an intervention.

Where rights affect the verdict, give their relational semantics. One possible stipulated interface pairs a claim held by \(i\) against \(j\) concerning \(\varphi\) with \(j\)'s corresponding duty to \(i\). A liberty to act means absence of a duty not to act in that interface; it does not entail another actor's duty to assist. A power concerns a valid transformation of specified normative relations, with liability naming another party's exposure to that power. An immunity concerns the absence of another party's specified power over a relation; it does not imply technical tamper resistance. Keep weak permission by absence of prohibition separate from explicit authorization when the application distinguishes them. These are candidate model definitions, not claims about the law of any jurisdiction.

Use a transition relation for valid changes of institutional state and a coupled realization model for physical or digital effects. An unauthorized act may have a physical effect; a digitally recorded event may lack the specified institutional validity. A permission rule blocks a Byzantine act only through an actual enforcement mechanism or a declared capability restriction. The specification should say whose rule system and recognition conditions are in force.

For public evidence, distinguish a fact, a witness artifact, a verifier's acceptance predicate, and the soundness theorem connecting acceptance to the fact under the fault model. Define evidence generation operationally. Do not define admissible evidence by the conflict-exclusion conclusion it is meant to prove. A verifier that rejects every artifact is vacuously sound; include attainable valid artifacts and any completeness or availability requirement the application needs.

Study fault-tolerant control, fault attribution, and accountability separately. Evidence sufficient for intervention may differ from evidence sufficient for assigning blame. Review, appeal, reversibility, and intervention proportionality can be specified design constraints; they do not follow as mathematical consequences of controlled invariance. Normative choices remain explicit inputs or unresolved alternatives.

Outputs: a minimal institutional model whose distinctions change a concrete verdict, one collapse counterexample, and a public-evidence contract with a non-vacuity witness. Assess the fixed-context evidence-refinement result above before claiming special monotonicity laws for any class of facts.

### R7 Extend through time, recovery, and changing membership

Evaluate logical membership removal separately from effective exclusion. Define effective exclusion relative to a target invariant and horizon: residual actions through all modeled channels are either prevented, bounded in the adversary envelope, or compensated within the proved control margin. It need not mean eliminating every physical capability. A revoked key does not automatically disable a valve, and isolating an actuator may remove indispensable correct capacity.

Analyze containment, substitution, repair, reintegration, and service continuity together when the proposed guarantee needs them. Reconfiguration changes the identity universe, fault interpretation, certificates, and evidence accepted across epochs. An old quorum proof does not automatically survive that change. For repaired actors, specify what state and keys may remain adversarial. If membership is optimized or strategically manipulated, recheck the fault-family assumptions.

For a continuous or hybrid extension, state solution existence, control regularity, disturbance class, sampling, delays, resets, and any exclusion of Zeno behavior. A control barrier certificate is a sufficient condition under specified hypotheses; failure to find one is not necessarily a proof of infeasibility. A delay margin obtained from a scalar drift bound is conditional on that bound throughout the interval and on the intervention available afterward. Summing unrelated latency estimates is not a general viability theorem.

Outputs: a checked timed or recovery fragment, or explicit proof obligations and a counterexample establishing why the initial discrete result does not transfer. This workstream also retains stochastic guarantees, privacy, rational incentives, and cross-institution authority as scoped extensions if the chosen example consumes them. Worst-case Byzantine tolerance does not establish incentive compatibility; slashing that changes incentives and revocation that changes effective capabilities require different arguments.

### R8 Build useful mathematical correspondences

Select mathematical accounts by the obstruction they can resolve. Candidate accounts include transition systems and games for strategy quantifiers, control and viability for feasible trajectories, epistemic semantics for indistinguishability, automata and contracts for execution restrictions and composition, and institutional semantics for validity and powers. This is a candidate allocation of work, not a theorem assigning each phenomenon to a unique discipline.

For every claimed bridge, supply the source and target objects, their context indices, the forward and any reverse translation, preserved queries or operations, the representation kernel, and the strategy or certificate transport. If organized categorically, state what objects and morphisms are and which composition laws have been proved. Use one-way sound refinement when equivalence is unsupported. A finite-state controller, a winning strategy, a knowledge-based rule, a barrier certificate, and a permissive governance regime are not automatically interchangeable encodings.

Compare state-invariant and trace-safety representations on the same model; include monitor or history state when needed. Compare observation-based policies with epistemic action conditions under their exact assumptions. Compare a discrete abstraction with a physical model using a realizable action map and an appropriate simulation relation. If the abstraction assumes central information unavailable to the implementation, ordinary trace inclusion may fail to transport the claimed controller; preserve the choice and information structure as well.

A useful strategy-transport target is a componentwise map \(\operatorname{lift}_i\) computable from actor \(i\)'s permitted local history and abstract action. For a declared trace relation \(R^\omega\), prove that every admissible concrete run under \(\operatorname{lift}(\pi^\#)\) has a related admissible abstract run under \(\pi^\#\), and that \(R^\omega\)-related runs transport the specific property in the required direction. A statewise existential concrete action may depend on hidden state and therefore does not supply such a local map. If clocks or stuttering are involved, state the observation and time correspondence; safety transport does not automatically preserve deadlines or progress. This is a proposed theorem interface whose realization and proof remain part of R8.

Two derivations count as a stronger cross-check only to the extent that they do not merely repeat the same unproved encoding assumption. An independent representation, separately implemented exhaustive checker, or direct counterexample search can expose a bad translation. Lean checking establishes the encoded theorem, not fidelity of the encoding to the physical or institutional target.

Outputs: a small map of useful proved, conditional, or failed correspondences and at least one applied transfer or discriminating failure. Do not require all disciplines to converge to an identical formalism. A boundary or failed correspondence can be a central research result.

## Benchmarks and comparison controls

Use a common scenario family to expose interactions while retaining small countermodels for specific failed implications. The family should contain a digital baseline and a sensor–actuator system. The following construction is proposed because it gives observation, actuation, and authority distinct consumers; it is not a universal benchmark taxonomy.

The digital instance is a fixed-slot replicated decision or register with explicit messages, signatures, quorum rules, and faulty identities. Distinguish correct replicas' committed prefixes from their tentative or view-local state. Agreement need not mean equality of every local implementation variable at every instant. Add a counterexample in which an agreed valid command fails to establish a separately specified external-world fact or effect.

For the physical instance, use a pressure system with an inlet, a relief mechanism, distributed measurements, delayed commands, and a possible manual or adversarial bypass. State the physical model and units. In a discrete abstraction, one possible balance is \(p_{t+1}=p_t+\Delta t\,g(p_t,u_t,b_t,w_t)\), where \(u_t\) is correct control, \(b_t\) a capability-constrained hostile input, and \(w_t\) a disturbance. Specify how flows become pressure changes and where the abstraction is valid. Choose numerical bounds only after defining the model; supply the abstraction error or explicitly confine the result to the discrete benchmark.

Specify both a safety region and a service requirement, including any lower pressure limit or required delivery that makes permanent shutdown inadequate. Start with a feasible trusted-interface instance. Add Byzantine measurements; then witness observations with uncertain pose or calibration; hostile actuation or bypass; communication and actuation delay; and exclusion/replacement. These are selectable extension axes, not a claim that their order is canonical. Test at least one interaction that independent single-axis analyses miss.

At each studied variant, compare a controller with full state and known faults, a pooled-information controller, and the actually distributed controller where those distinctions matter. Maintain a common plant and objective for each comparison. If one design changes hardware, sensing, trust, or admissible attacks, record that as a changed context rather than attributing its performance solely to a better algorithm.

Report reachable and winning regions or certified approximations with their direction, counterexample traces, fault and timing assumptions, service outcomes, and the intervention that changes the verdict. Use cost, false-attribution rates, evidence completeness, or authority concentration only when they have defined measurements and consumers. Simulated frequency is not a worst-case guarantee.

## Literature tasks and checked entry points

Search by the obligations above, including work that could already discharge or invalidate a proposed contribution. For each imported result, record the exact theorem or passage, definitions, hypotheses, conclusion, source version, and translation into the local model. Distinguish bibliographic verification, statement verification, proof reconstruction, implementation checking, and empirical replication. Search results and abstracts locate candidates; theorem-level imports require the theorem and its conditions.

Before substantial original work on an obligation, integrate a delegated related-work assessment and identify the closest result, the exact remaining gap, and whether import, adaptation, or a new attempt is warranted. Apply the per-obligation readiness and search-stopping rules in [EXECUTION.md](EXECUTION.md). Frontier discovery is an evidence-bearing research step; an unsuccessful search does not establish that humanity has left a problem open.

The following entry points were checked on 2026-10-04 to the stated scope. `[✓]` is limited to that scope and does not certify a new application. In a later session recheck any load-bearing imported result before assigning that session's `[✓]`; use `[~]` for unconfirmed support. No novelty claim is established by this list.

| ID | Primary source and checked scope | Research consumer |
|---|---|---|
| S1 | [Yin et al., HotStuff, version 6](https://arxiv.org/html/1803.05069v6), `[✓]` Sections 3–4 protocol structure and stated safety/progress arguments inspected. | R1 exact baseline and certificate semantics; complete its encoding audit before claiming formal verification. |
| S2 | [Fawzi, Tabuada and Diggavi, Secure estimation and control for cyber-physical systems under adversarial attacks](https://arxiv.org/abs/1205.5073), `[✓]` abstract and bibliographic record. It reports resilient linear-system estimation and an output-feedback separation result under its attack model. | R3–R4 prior art; retrieve the exact separation theorem and compare its information and attack assumptions. |
| S3 | [Mitra and Sundaram, Byzantine-Resilient Distributed Observers for LTI Systems](https://arxiv.org/abs/1802.09651), `[✓]` abstract. It relates distributed estimation to measurement and communication redundancy. | R2 and R3; inspect the fault model, source sets, graph conditions, and convergence guarantees. |
| S4 | [Naqvi, Khan and Vaidya, Exact Byzantine Consensus Under Local-Broadcast Model](https://arxiv.org/abs/1811.08535), `[✓]` abstract and synchronous reliable-local-broadcast model. | R2 channel restrictions versus evidence; import connectivity results only after checking their exact hypotheses. |
| S5 | [Finkbeiner and Schewe, Uniform Distributed Synthesis](https://finkbeiner.groups.cispa.de/publications/2005-uniform-distributed-synthesis/), `[✓]` primary publication page and paper's information-fork characterization inspected for its synchronous architecture setting. | Select a decidable architecture or a bounded synthesis problem; finite syntax alone does not establish decidability. |
| S6 | [Moses, Relating Knowledge and Coordinated Action](https://arxiv.org/abs/1606.07525), `[✓]` abstract and bibliographic record. | R1 and R8 knowledge-of-preconditions hypotheses; necessary versus sufficient epistemic conditions. |
| S7 | [Ames et al., Control Barrier Function Based Quadratic Programs for Safety Critical Systems](https://arxiv.org/abs/1609.06408), `[✓]` abstract. | R7 continuous-time certificates; inspect regularity, feasibility, solution, and robustness assumptions before transfer. |
| S8 | [Roth and McMillin, Physical Attestation of Cyber Processes in the Smart Grid](https://scholarsmine.mst.edu/comsci_facwork/1808/), `[✓]` authors' institutional record and abstract only. | R2 physical evidence and its trust boundary; theorem and mechanism details remain `[~]`. |
| S9 | [Lamport, Shostak and Pease, The Byzantine Generals Problem](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/The-Byzantine-Generals-Problem.pdf), `[✓]` oral/signed-message distinction and stated communication assumptions inspected. | R1 threshold claims must remain indexed to their model; no universal `3f+1` law is assumed. |
| S10 | [Castro and Liskov, A Correctness Proof for a Practical Byzantine-Fault-Tolerant Replication Algorithm](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/01/tm590.pdf), `[✓]` introduction's use of invariant assertions and simulation relations and explicit safety-only proof scope. | R1 and R8 prior art for state/trace refinement; translating BFT into invariant language is not by itself a new contribution. |

Additional targeted searches should cover supervisory control under sensor and actuator attacks, decentralized control and imperfect-information games, distributed runtime assurance and shield synthesis, collaborative perception and sensor attestation, active fault diagnosis, dynamic reconfiguration, cryptographic accountability, public-evidence semantics, capability security, and formal institutional/deontic models. Treat these as search directions, not unchecked theorem citations. Evaluate claimed sensor-witness systems by their observable variables and fault assumptions; evaluate empirical detectors separately from worst-case inference results. Include counterexamples and negative results in the search.

Record search coverage and useful unsearched areas. A claim that no prior result was found is bounded by the actual search. If an existing theorem solves a target, import it with a checked refinement and redirect original work to the remaining gap. If a theorem invalidates the proposed organization, revise the organization.

## Autonomous execution and branching

Begin by reading this handoff, [EXECUTION.md](EXECUTION.md), and the verification record. Establish a clean research worktree at an explicit commit containing the complete packet, verify the assigned paths, and run the supplied checks there. Delegate the initial related-work searches while clarifying the concrete model and target property. Integrate their results before selecting the first substantial original-work attempt. R1 provides shared semantics; R2 and R3 provide evidence and capability interfaces; R4 tests their assembly; R5 tests whether less coordination suffices; R6 and R7 supply constraints and extensions; R8 records useful translations throughout. This dependency structure is warranted by what the composed control theorem consumes, not by disciplinary chapter order.

Use a result ledger with stable claim identities when later proofs or artifacts consume them. A record should retain statement, context, status, support, dependencies, and residuals sufficient to resume or invalidate a dependent claim. A global disclaimer does not qualify an overstrong local theorem. Keep definition, conjecture, proved result, cited result, interpretation, and empirical finding distinct. Institutional acceptance is a separate field or explicit boundary, not another evidence grade.

Choose attacks appropriate to the obstruction. Indistinguishable executions can refute information sufficiency. A smallest conflicting certificate can expose a protocol invariant. A counterstrategy can refute control feasibility. Induction can establish a proposed invariant once its premises are constructible. A simulation can transport a safety certificate if it preserves the required choices and observations. Select a method for a named theorem rather than importing a mathematical apparatus because its terminology resembles the problem.

The decisive branches are as follows. If the uniform action set is empty, distinguish exact infeasibility from conservative abstraction failure before choosing a refinement. If synthesis is undecidable in the proposed generality, choose a justified architectural, memory, or horizon restriction and mark what it loses; failure of a bounded search is not unrestricted impossibility. If a component assumption cannot be enforced, bounded, or verified, retain it explicitly or weaken the guarantee. If a bridge fails, retain the counterexample and seek a weaker useful transport. If a normative choice changes the mission, expose alternatives and proceed with conditional mathematical work. If a proof attempt stalls, state the precise missing lemma and pursue another unblocked obligation.

Aim for substantive research before polishing exposition. Produce at least one integrated positive or impossibility result connecting two of information, capabilities, coordination, and realized effects, with a concrete instance. A conditional composition theorem is useful when its premises have constructive witnesses and its exclusions are informative. The elementary companion lemmas alone do not fulfill this objective. Cover every workstream with an honest result or residual; do not manufacture proofs to fill the coverage record.

Before closure, revisit whether the chosen model still represents the desired control problem. Check for hidden centralized information, state-dependent actions chosen without knowledge, fault budgets reset between components, inconsistent timing, impossible fallback, strengthened environment assumptions, and specification weakening that merely makes the theorem easy. Prefer an exhibited countermodel or checked survival record to verbal reassurance.

## Artifacts and verification requirements

Produce a readable synthesis supported by separate executable and proof artifacts where needed. A 6,000–10,000-word synthesis is a planning guide rather than a quota; retain material definitions, assumptions, results, and residuals even when a different size serves the work. The entry document should explain the achieved result, how it relates to Byzantine control and the BFT baseline, the exact scope of verification, and the next discriminating work.

Useful maintained outputs are a semantic model and assumption record; a theorem/counterexample ledger with proofs; executable digital and physical instances; a primary-source comparison; the assumption-replacement and bridge results; and a concise resumption TODO. These roles may share files when their definitions and uses are inseparable. Keep one maintained home for each shared definition. Reproduce necessary claims in the resulting research package instead of making informal notes prerequisites.

Use Lean for discrete mathematical claims that benefit from mechanization. [Foundations.lean](Foundations.lean) imports only the installed standard library. The pinned toolchain is Lean 4.33.0. From this directory, run `./verify.ps1`; alternatively invoke a matching installed Lean binary on `Foundations.lean`. The script resolves the pinned binary from an existing elan installation and changes no global toolchain setting. It accepts `-LeanExecutable` for another installation path. Its axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`; these are Lean logical foundations, not task-specific assumptions.

Extend formalization where it checks a load-bearing obligation. Keep open propositions outside the proved module or explicitly marked as hypotheses in a theorem whose conditional conclusion is intended. A completed theorem must not depend on `sorry`, `admit`, a custom axiom restating the target, or an unrecorded trust extension. Inspect `#print axioms` for exported results. Prefer kernel-checked proof terms and `decide`; a native computation or external solver can be useful evidence but needs its different trust boundary recorded. Classical existence proofs do not automatically extract executable controllers.

For finite experiments, declare state, action, horizon, policy-memory, and fault bounds. Distinguish exhaustive search of that finite space from sampled testing. Export a counterexample trace or a strategy with a checkable invariant; solver success should be independently replayable where practical. Infinite-horizon conclusions require a proved invariant, fixed-point argument, or another appropriate certificate. For continuous models, state discretization and numerical error obligations; trajectory plots alone cannot establish universal safety.

Verification must assess semantic adequacy as well as proof elaboration. Check theorem statements against their intended control claims, confirm satisfiable assumptions and nonempty behavior, and inspect a concrete example that exercises the claimed distinction. Generated tests that merely repeat an implementation without an independent specification do not establish that specification. Self-review is a first pass; queue genuinely independent verification when it has not occurred.

The final acceptance test for the research increment is reconstructibility: a reader using only the delivered package and identified primary sources can recover the target, instantiate the model, reproduce the claimed checks, identify each removed and retained assumption, distinguish proved from open statements, and understand what changes if an assumption fails. Every claimed BFT recovery and mathematical bridge has a stated preservation law. Every workstream has a disposition. The integrated result has been challenged across component boundaries. The remaining TODO contains live obligations rather than authoring history.

Close with the strongest supported conclusion and its exact limits. Preserve failures that change the theory. Commit the artifacts on the isolated integration branch with a session record stating the moves chosen, result statuses, material semantic choices and corrections, bounded negative searches, and what a resuming session must know. Report its worktree path and commit; leave the dirty primary checkout and unrelated work outside those commits.
