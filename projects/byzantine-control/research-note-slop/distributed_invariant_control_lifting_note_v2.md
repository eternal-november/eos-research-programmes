# From Byzantine Fault Tolerance to Distributed Invariant Control
## A state-space lifting problem, research instrument, and agenda

**Status.** Provisional research note. This document is not a finished theory and should not be read as one. Its purpose is to make the generalization problem precise enough that a human researcher or a language model can continue the work without prematurely deciding what the correct abstraction must be.

**Working name.** The neutral name is **Distributed Invariant Control**. The Byzantine-qualified subproblem is **Distributed Invariant Control under Byzantine conditions**. The phrase “Byzantine control” is tolerable shorthand, but it is not the preferred technical name because it names the disturbance model rather than the controlled object.

---

## 0. Methodological rule

The core discipline of this note is:

> Every variable used by the controller must be either controlled, inferred, or assumption-bounded.

If a controller uses “state,” the theory owes a state-estimation argument. If it uses “capability,” it owes a capability-estimation argument. If it uses “honest majority,” it owes a membership and corruption model. If it uses “sensor independence,” it owes a fault-domain decoupling argument. If it uses “actuator obeys,” it owes an actuation contract. If it uses “environment behaves,” it owes a disturbance bound. If it uses “model is valid,” it owes a model-validity monitor or an explicit trusted assumption.

The note should be used in that spirit. Do not convert provisional mechanisms into axioms. Do not infer that coercive action, institutional enforcement, or physical removal is primitive. Those may be necessary in some lifts; in other lifts they are irrelevant. The research problem is to find the conditions under which a lift from BFT to more general invariant control exists, and to classify the ways the lift fails.

---

## 1. The minimal research thesis

Classical Byzantine fault tolerance can be interpreted as distributed control over a restricted object: a replicated protocol state, an execution trace language, an agreement relation, or a certified decision process. The generalization problem is to characterize when that controlled object can be enlarged.

In its most compact form:

\[
\text{BFT consensus}
\quad\leadsto\quad
\text{BFT sensing and inference}
\quad\leadsto\quad
\text{BFT control over generalized state.}
\]

The first arrow is not optional. Once the controlled state is no longer constituted entirely by the replicated protocol, the controllers do not get the state for free. They act through observations, evidence, inference, diagnosis, and certification. The object of agreement should often be not a point state, but a certified information object: an ambiguity set, diagnosis set, posterior set, proof bundle, certificate graph, or robust estimate.

Thus, for a generalized state \(x_t\), the safety claim should usually not be:

\[
u_t \text{ is safe for } x_t.
\]

The controller does not directly possess \(x_t\). A more honest claim is:

\[
x_t \in B_t
\quad\text{and}\quad
u_t \text{ is safe for every } x\in B_t.
\]

Here \(B_t\) is a certified information state produced under explicit observation, fault, timing, and model assumptions. The central bridge from BFT to control is therefore not only consensus over commands. It is agreement over a safe epistemic envelope.

---

## 2. First reconstruct BFT as control; do not choose too early

There are several plausible control-theoretic reconstructions of BFT. They are related but not equivalent, and each suggests a different generalization.

### 2.1 Agreement-manifold reconstruction

Let \(q_i(t)\) be the local protocol or application state of replica \(i\), and let \(H\) be the set of correct replicas. A safety property can be represented as an agreement relation

\[
\Delta_H = \{q : q_i = q_j \text{ for all } i,j\in H\}.
\]

The BFT protocol is then a distributed controller that keeps the correct replicas on, or recoverably near, \(\Delta_H\) despite arbitrary behavior by faulty replicas within the threat model.

This reconstruction connects BFT to controlled invariance, but it risks overidentifying consensus with control. It is strongest when the object being controlled is the replicated state itself.

### 2.2 Trace-language reconstruction

A distributed protocol can also be viewed as constraining executions:

\[
\operatorname{Trace}(P,A) \subseteq L_{safe},
\]

where \(A\) ranges over adversarial strategies satisfying the Byzantine fault model. Safety is a prefix-closed language property; liveness is an eventuality or fairness-conditioned progress property.

This reconstruction may be more faithful to distributed computing, where the “global state” is often a semantic convenience rather than a directly observed control state.

### 2.3 Epistemic reconstruction

A third reconstruction treats BFT as control over admissible knowledge, certificates, or decision authority. The protocol regulates when correct processes may move from uncertainty to irreversible commitment:

\[
h_i(t) \mapsto \operatorname{decide}_i(v),
\]

where \(h_i(t)\) is process \(i\)’s local history. Quorum certificates, authentication, non-equivocation, view changes, and finality rules become mechanisms for shaping distributed epistemic state.

This reconstruction becomes central once the generalized system needs to infer state, capabilities, or causal hypotheses rather than merely agree on a client request.

### 2.4 Use all three as candidate base objects

The lifting problem should not assume from the start that “state” is the only controlled object. A base BFT system may control a state relation, a trace language, an epistemic commitment structure, or a combination. The research program should record which reconstruction is being lifted in each theorem or example.

---

## 3. The state-space lifting problem

Let a base BFT-controlled system be described abstractly as

\[
\mathcal S = (S,U,W,F,H,K),
\]

where \(S\) is the base state or semantic object, \(U\) is the protocol action space, \(W\) is the disturbance or Byzantine behavior class, \(F:S\times U\times W\rightrightarrows S\) is a transition relation, \(H_i:S\to Y_i\) describes local observations, and \(K\subseteq S\) is the base safety set or admissible relation.

A distributed policy is a family

\[
u_i(t)=\pi_i(h_i(t)),
\]

where \(h_i(t)\) is the local history of process \(i\). A safety theorem has the rough form

\[
s_0\in K
\Longrightarrow
s_t\in K\quad\text{for all }t,
\]

for every admissible Byzantine strategy and schedule.

Now introduce a generalized state space \(X\) and a projection

\[
p:X\to S.
\]

The projection identifies the base BFT state contained in, abstracted from, or induced by the richer state. The generalized system is

\[
\widetilde{\mathcal S}=(X,\widetilde U,\widetilde W,\widetilde F,\widetilde H,\widetilde K),
\]

where \(\widetilde K\subseteq X\) is the generalized invariant.

The core research question is:

\[
\begin{gathered}
\text{Given a BFT-controlled base system }S\text{ and a state extension }p:X\to S,\\
\text{what observation, inference, consensus, action, actuation, timing,}\\
\text{decoupling, and recovery conditions are sufficient or necessary}\\
\text{to preserve an invariant }\widetilde K\subseteq X?
\end{gathered}
\]

This is a lifting problem. A successful lift should explain how the base BFT mechanism is used, what additional structure is required, and which assumptions are no longer inherited from the base protocol.

Compatibility between the base and generalized systems might be expressed by a simulation, refinement, or conservative-extension condition such as

\[
p(\widetilde F(x,\widetilde u,\widetilde w))
\subseteq
F(p(x),u,w),
\]

but that condition is only schematic. Different reconstructions of BFT will require different compatibility notions.

---

## 4. Certified sufficiency, not complete truth

The generalized controller usually cannot know the full state \(x\in X\). It may not need to. It needs certified information sufficient for safe action.

Let

\[
\alpha:X\to Z
\]

be a control-relevant abstraction. The controller may only need to infer \(z_t=\alpha(x_t)\), or an ambiguity object \(C_t\subseteq Z\) such that \(z_t\in C_t\). When the invariant factors through \(Z\), full knowledge of \(X\) is unnecessary.

A clean abstraction condition is:

\[
\alpha(x)=\alpha(x')
\Longrightarrow
\bigl(x\in \widetilde K \iff x'\in \widetilde K\bigr),
\]

or, for action selection,

\[
\alpha(x)=\alpha(x')
\Longrightarrow
U_{safe}(x)=U_{safe}(x').
\]

When this fails, the abstraction is too coarse. Two concrete states collapsed into the same abstract state may require different safe actions. That is not an estimation problem alone; it is a modeling error.

The invariant should therefore drive the state ontology, not the reverse. For a purely replicated register, protocol state may be sufficient. For a physical plant, material variables become relevant. For an authority invariant, credentials, delegation, and revocation state may be relevant. For a capability invariant, actual access and bypass channels may be relevant. There is no universal product decomposition of \(X\) that should be asserted before the invariant is known.

A candidate decomposition, used only when demanded by the invariant, is

\[
X
=
X_{plant}
\times X_{protocol}
\times X_{belief}
\times X_{capability}
\times X_{authority}
\times X_{evidence}
\times X_{model}
\times X_{environment}.
\]

The right question is not whether all these factors are present. It is which hidden variables can falsify the guarantee if omitted.

---

## 5. The generalized control loop

The base BFT abstraction often makes evidence, input, decision, and transition appear close together. Generalized invariant control separates them:

\[
X_t
\rightarrow O_t
\rightarrow E_t
\rightarrow B_t,H_t
\rightarrow D_t
\rightarrow U_t
\rightarrow X_{t+1}
\rightarrow O_{t+1}.
\]

The terms are:

| Symbol | Object | Control significance |
|---|---|---|
| \(X_t\) | actual generalized state | the thing whose invariant is at stake |
| \(O_t\) | raw observations | sensor readings, reports, logs, attestations, measurements |
| \(E_t\) | admissible evidence | observations filtered by provenance, authentication, freshness, consistency, and admissibility rules |
| \(B_t\) | certified information state | an ambiguity set, posterior set, estimate set, proof object, or certificate bundle satisfying a soundness guarantee |
| \(H_t\) | live diagnosis or causal hypotheses | fault hypotheses, attack hypotheses, model-regime hypotheses, capability hypotheses |
| \(D_t\) | agreed decision | the jointly selected policy branch, intervention class, or certificate-bearing decision |
| \(U_t\) | realized control input | the actuator-level command or intervention actually applied |
| \(X_{t+1}\) | resulting state | what the world or generalized system becomes |
| \(O_{t+1}\) | verification observations | evidence used to check whether the intended transition occurred |

This decomposition is not just notation. Each arrow can fail in a different way. A theory that says “BFT plus control” but does not specify these arrows has not yet said what is being controlled.

---

## 6. Byzantine-resilient sensing and inference

The natural epistemic primitive is **Byzantine-resilient observability**.

Classical observability asks whether the state can be inferred from outputs. Byzantine-resilient observability asks whether the control-relevant state or abstraction can be inferred when some sensors, reporters, logs, communication links, estimators, or models may be adversarial, buggy, stale, spoofed, strategically incomplete, or commonly compromised.

A useful negative condition is indistinguishability under incompatible safe action.

Let \(x,x'\in X\) be two possible states such that

\[
U_{safe}(x)\cap U_{safe}(x')=\varnothing.
\]

If an admissible adversary can make every correct controller receive the same admissible observation history under \(x\) as under \(x'\) until the recoverability horizon expires, then no distributed controller can guarantee the invariant from both states.

The positive version is not simply “the state is observable.” It is:

> Every pair of states that require incompatible control must become distinguishable, modulo the permitted disturbance and fault model, before the system exits the recoverable region.

A controller may agree not on a single estimate \(\hat x_t\), but on a certified envelope

\[
x_t\in B_t.
\]

The safe action condition is then

\[
u_t\in \bigcap_{x\in B_t}U_{safe}(x),
\]

or, equivalently,

\[
\operatorname{Post}(B_t,u_t,\widetilde W)\subseteq \widetilde K.
\]

If this set is empty, the system has entered an epistemic-control failure mode. It may possess consensus, and all correct controllers may be honest, while still not knowing enough to act safely.

---

## 7. Diagnosis and agreement on disagreement

State estimation and fault diagnosis should not be collapsed. A system may know that an invariant is threatened without knowing whether the cause is sensor corruption, actuator failure, environmental regime change, model error, or controller compromise.

Represent this by a hypothesis object \(H_t\). The action must be safe across the joint uncertainty \((B_t,H_t)\), or the controller must choose a diagnostic action that reduces uncertainty while remaining inside the recoverable set.

The correct agreement object may therefore be:

\[
(B_t,H_t),
\]

not \(\hat x_t\), and not a single accusation such as “node \(i\) is Byzantine.”

This motivates the phrase **agreement on disagreement**. The system may need to agree on the set of remaining possible states, faults, and capabilities rather than prematurely force a single explanation. Fault detection, fault attribution, fault containment, and fault punishment are separate operations. Invariant control often needs detection and containment before attribution is settled. Human institutions may require attribution and punishment; that is a separate specification burden.

---

## 8. Capability inference

Capabilities should not be read directly from a role table. In the generalized setting, capability is state.

For actor or component \(i\), let

\[
\mathsf{Cap}_t(i)\subseteq A
\]

be the set of actions that \(i\) can actually cause or materially influence at time \(t\). The controllers rarely know this exactly. They may maintain a certified upper bound

\[
\widehat{\mathsf{Cap}}_t(i)\supseteq \mathsf{Cap}_t(i),
\]

and sometimes a lower bound

\[
\underline{\mathsf{Cap}}_t(i)\subseteq \mathsf{Cap}_t(i).
\]

The upper bound matters for safety: what could a Byzantine or malfunctioning actor still do? The lower bound matters for liveness and recovery: what can an honest or repaired actor still reliably do?

A capability-aware invariant controller reasons against upper bounds:

\[
\forall a\in \widehat{\mathsf{Cap}}_t(i),
\quad
\text{the invariant remains preserved or recoverable.}
\]

If the upper bound is too large, the system must either shrink it, compensate for it, or weaken its guarantee. Shrinking the certified capability envelope can be done by revocation, isolation, rate limiting, routing changes, interlocks, escrow, physical exclusion, legal intervention, or redesign. None of these is primitive. Each is one way to alter the capability state or its certified bound.

This reframes the earlier “police” intuition. The abstract requirement is not a police force. It is a means of making invariant-relevant capability claims true, bounded, or irrelevant. In some domains that requires physical or institutional force. In others it is solved cryptographically, mechanically, economically, architecturally, or not at all.

---

## 9. Action classes: epistemic and causal control

The action space should not contain only corrective interventions. Some actions are epistemic. Some change topology. Some restore capacity. A provisional decomposition is

\[
\widetilde U
=
U_{observe}
\cup U_{probe}
\cup U_{decide}
\cup U_{actuate}
\cup U_{reconfigure}
\cup U_{recover}.
\]

| Action class | Role in the lifted problem | Failure if omitted |
|---|---|---|
| \(U_{observe}\) | collect passive evidence | the controller treats absence of information as state knowledge |
| \(U_{probe}\) | actively distinguish states, faults, or capabilities | hidden states remain indistinguishable until escape |
| \(U_{decide}\) | commit to a policy branch or certificate | correct controllers cannot coordinate irreversible steps |
| \(U_{actuate}\) | change the plant or generalized state | decisions do not become transitions |
| \(U_{reconfigure}\) | alter membership, routing, authority, sensing, or control topology | the system cannot contain compromised channels |
| \(U_{recover}\) | restore state, trust, capacity, or service | exclusion and failover consume the system |

The diagnostic class \(U_{probe}\) is easy to understate. A safe system may need to challenge a sensor, send a canary command, force a fresh attestation, compare independent measurements, temporarily slow a process, trigger a controlled failover, or perturb a plant inside safe margins in order to distinguish hypotheses. This is active epistemic control. It is not merely monitoring.

---

## 10. Disturbance algebra, not one Byzantine blob

The word “Byzantine” is too blunt if left untyped. Generalized invariant failure may arise from malice, bugs, model misspecification, distribution shift, rare physical regimes, operator error, ambiguous specifications, adversarial-but-legal behavior, rational exploitation, or common-mode accidents.

A disturbance model should have structure:

\[
\widetilde W
=
W_{Byz}
\cup W_{bug}
\cup W_{edge}
\cup W_{env}
\cup W_{strategic},
\]

or, more carefully,

\[
\widetilde W = W_1\oplus W_2\oplus\cdots\oplus W_m,
\]

where \(\oplus\) is not ordinary union unless the components are independent and composable. Composition rules must specify which disturbances can occur together, which share causes, and which exhaust the same resource or fault budget.

The attack surface also depends on where the disturbance enters the loop.

| Loop segment | Example disturbance class | Required specification |
|---|---|---|
| \(X\to O\) | sensor spoofing, blind spots, calibration drift, adversarial environment | measurement assumptions and coverage |
| \(O\to E\) | forged provenance, replay, log tampering, selective reporting | evidence admissibility and freshness rules |
| \(E\to B\) | poisoned inference, correlated sensor failure, bad model, adversarial examples | estimator robustness and model validity |
| \(B,H\to D\) | consensus faults, equivocation, quorum mistakes, timing failure | agreement and decision assumptions |
| \(D\to U\) | invalid authorization, confused deputy, privilege escalation | authority semantics and command validity |
| \(U\to X\) | actuator compromise, command nonexecution, physical bypass, delayed effect | actuation model and mediation assumptions |
| \(X_{t+1}\to O_{t+1}\) | unverifiable effects, stale feedback, deceptive receipts | post-action verification |
| cross-layer | shared clock, root key, operator, software stack, vendor, model, incentive | fault-domain dependency model |

A single scalar such as “up to \(f\) Byzantine nodes” is usually too scale-free. It matters whether the corrupted components are sensors, estimators, validators, actuators, auditors, identity providers, model maintainers, operators, or recovery agents.

---

## 11. Fault-domain decoupling and assume–guarantee contracts

A generalized theory must be compositional or it will not scale. But compositionality is only sound when the relevant failure modes decouple.

A subsystem \(M_j\) should export a contract

\[
A_j \Rightarrow G_j,
\]

where \(A_j\) is the assumption under which the subsystem operates and \(G_j\) is the guarantee it supplies. In this problem those contracts need at least five components:

\[
\mathcal C_j=(A_j,G_j,\Phi_j,T_j,R_j),
\]

where \(\Phi_j\) is the tolerated disturbance or adversary class, \(T_j\) is a timing and freshness envelope, and \(R_j\) is a resource or redundancy requirement.

A sensing layer might export:

\[
A_{sense}: \text{ at most } f_s \text{ of } n_s \text{ sensors corrupt, delay}\le\delta_s,
\]

\[
G_{sense}: x_t\in B_t \text{ and } \operatorname{diam}(B_t)\le \epsilon_s \text{ within }\tau_s.
\]

The controller layer can consume that guarantee:

\[
A_{control}: x_t\in B_t,\ \operatorname{diam}(B_t)\le\epsilon_s,
\]

\[
G_{control}: u_t\in U_{safe}(B_t).
\]

The actuation layer then needs its own contract:

\[
A_{act}: \text{valid command }u_t\text{ under actuator fault budget }f_a,
\]

\[
G_{act}: X_{t+1}\in \operatorname{Post}(X_t,u_t,W_a).
\]

Composition requires not only

\[
G_j\models A_k,
\]

but also consistency of the fault and dependency assumptions. A sensor ensemble and an adjudicator should not be counted as independently fault-bounded if they share the same model, time source, root key, software stack, operator, physical enclosure, training data, vendor, or economic incentive.

A useful rule is:

> Components may be treated as independently fault-bounded only to the extent that the mechanisms by which they fail are non-overlapping relative to the adversary and disturbance model.

This is a major difference between replication and resilience. Replication multiplies components. Resilience requires controlling common-mode dependence.

---

## 12. Invariant classes and truth-makers

“Invariant” is not one kind of object. Different invariants have different truth-makers, and therefore require different evidence and actuation semantics.

| Invariant class | Example | Truth-maker | Typical control burden |
|---|---|---|---|
| protocol invariant | no two correct replicas commit conflicting values | message histories and protocol state | consensus, authentication, non-equivocation |
| data invariant | balance is nonnegative | application state and transition rules | transaction validation and rollback semantics |
| physical invariant | pressure stays below threshold | material dynamics | sensing, robust estimation, actuation, timing |
| capability invariant | actor lacks ability to perform action \(a\) | actual access and influence channels | mediation, verification, exclusion or compensation |
| authority invariant | only authorized actors can command | credential and delegation state | identity, revocation, threshold authorization |
| epistemic invariant | controllers know enough to act safely | belief and certificate state | robust inference and freshness |
| service invariant | system retains minimum function | topology, resources, redundancy | recovery, degraded modes, spare capacity |
| audit invariant | decisions remain reconstructible | evidence and log state | provenance, retention, tamper evidence |
| model invariant | controller assumptions remain valid | relation between model and environment | monitoring, adaptation, regime detection |

The list is not a proposed universal ontology. It is a diagnostic check. If an invariant’s truth-maker lies outside the modeled state and outside the assumption boundary, the guarantee is not yet real.

---

## 13. Safety theorem template

A minimal compositional safety theorem should separate estimation, agreement, action selection, and actuation.

Let \(X\) be the generalized state space, \(\widetilde K\subseteq X\) the invariant, and \(\widetilde W\) the disturbance class. Define

\[
\operatorname{Post}(B,u,W)
=
\{x'\mid \exists x\in B,\exists w\in W,\ x'\in \widetilde F(x,u,w)\}.
\]

A Byzantine-resilient estimator provides a sound information object:

\[
\forall \widetilde w\in \widetilde W,
\quad
x_t\in B_t.
\]

A robust controller selects an action satisfying

\[
\operatorname{Post}(B_t,u_t,\widetilde W)\subseteq \widetilde K.
\]

An actuation contract ensures that the actual transition belongs to the modeled post-set. Then safety follows by induction:

\[
x_t\in B_t
\quad\land\quad
\operatorname{Post}(B_t,u_t,\widetilde W)\subseteq \widetilde K
\quad\Longrightarrow\quad
x_{t+1}\in \widetilde K.
\]

This theorem is intentionally modest. Its value is the decomposition of obligations:

\[
\text{sound estimation}
+
\text{agreement on the information/action object}
+
\text{robust action selection}
+
\text{valid actuation semantics}
\Rightarrow
\text{invariance.}
\]

BFT may enter separately at each stage:

\[
\text{BFT sensing/inference}\Rightarrow x_t\in B_t,
\]

\[
\text{BFT consensus}\Rightarrow \text{correct controllers agree on }B_t,H_t,u_t,
\]

\[
\text{BFT actuation}\Rightarrow \operatorname{Post}(B_t,u_t,\widetilde W)\text{ is the right transition envelope.}
\]

The theorem should not be presented as the final theory. It is a skeleton that forces assumptions to be assigned to the right layer.

---

## 14. Non-liftability templates

A serious research program needs impossibility results as much as architectures. The following templates are more important than any proposed mechanism.

### 14.1 Observational non-liftability

If two states requiring disjoint safe actions are indistinguishable to all correct controllers until the recoverability horizon expires, no distributed controller can preserve the invariant from both.

This is the natural control analogue of distributed indistinguishability arguments.

### 14.2 Abstraction non-liftability

If \(\alpha(x)=\alpha(x')\) but \(x\) and \(x'\) differ in invariant truth or safe action sets, no controller using only \(\alpha\) can guarantee the invariant.

This blocks fake state generalizations that omit control-relevant hidden variables.

### 14.3 Actuation non-liftability

If, for some certified information state \(B\),

\[
\forall u,
\quad
\operatorname{Post}(B,u,\widetilde W)\nsubseteq \widetilde K,
\]

then no action available to the controller can guarantee safety from that information state. Consensus over an action cannot repair absence of a safe controlled predecessor.

### 14.4 Mediation non-liftability

If an adversarial actor retains an unmediated transition that can drive the system outside \(\widetilde K\) before detection and compensation, then a protocol-level removal or certificate cannot guarantee the generalized invariant.

This is the formal version of the intuition that some external-world invariants require effective capability control. It should not be phrased as “there must be police.” It should be phrased as: the transition relation contains an unbounded or too-fast adversarial edge.

### 14.5 Decoupling non-liftability

If two contracts rely on independent fault bounds but share a common failure mechanism that the adversary can exploit, the composed theorem is unsound. This is not a rare implementation detail; it is one of the main ways generalized control claims become fictional.

### 14.6 Timing non-liftability

If the minimum time required for observation, inference, agreement, authorization, actuation, and verification exceeds the escape time from the recoverable set, safety is impossible under that architecture. The scalar inequality

\[
\tau_{obs}+\tau_{inf}+\tau_{agree}+\tau_{act}<\tau_{escape}
\]

is only a rough diagnostic. A real theorem should use reachable sets or viability kernels.

### 14.7 Recovery non-liftability

If containing or removing a faulty component eliminates indispensable sensing, actuation, authority, or service capacity, the defense itself may destroy the invariant. Exclusion and substitution are coupled; neither should be analyzed alone.

---

## 15. Lift failure taxonomy

The agenda should be organized around lift failures. Start with a BFT-controlled base object. Extend the state. Identify which condition breaks.

| Failure class | Formal symptom | Practical reading |
|---|---|---|
| observability failure | unsafe states are indistinguishable within the horizon | the system cannot know what is happening soon enough |
| identifiability failure | fault or causal source cannot be narrowed enough | the system cannot know what to isolate, compensate, or probe |
| inference failure | evidence does not imply a sound, useful \(B_t\) | the system cannot construct the control-relevant envelope |
| consensus failure | correct controllers cannot agree on \(B_t,H_t\), or \(u_t\) | the system cannot coordinate |
| robust-action failure | \(\bigcap_{x\in B_t}U_{safe}(x)=\varnothing\) | the system knows too little, waited too long, or lacks authority |
| actuation failure | commanded transitions are not guaranteed | decisions do not constrain the world |
| verification failure | effects cannot be confirmed | the loop does not close |
| decoupling failure | assumed independent faults share a cause | the proof double-counts resilience |
| model-closure failure | adversary uses unmodeled transition channels | the guarantee is outside the actual system |
| recovery failure | removing bad components destroys service or control | defense collapses the defended system |
| adaptation failure | environment or adversary changes faster than model updates | the controller preserves yesterday’s invariant |
| specification failure | invariant is underspecified, inconsistent, or non-operational | the control objective is not yet a real target |

This table is an instrument. For any candidate theory, find the smallest example in which the proposed lift fails and classify the failure. A theory that cannot generate its own counterexamples is probably not yet mature.

---

## 16. Research agenda

The agenda below is ordered by dependency, not by importance. Later items may motivate earlier definitions, but they should not be smuggled into them.

### 16.1 BFT-as-control reconstruction

Produce several faithful reconstructions of BFT as control: agreement-manifold, trace-language, and epistemic-certificate versions. Identify what each reconstruction treats as state, action, disturbance, observation, safety, and liveness.

Question: Which parts of BFT are genuinely control-theoretic, and which are artifacts of discrete replicated protocols?

### 16.2 State-space lifting and refinement

Define extensions \(p:X\to S\), abstractions \(\alpha:X\to Z\), compatibility relations, and conservative-extension conditions. Determine when an invariant over \(X\) factors through \(S\), through \(Z\), or through neither.

Question: When is the generalized invariant really new, and when is it just a restatement of the base protocol invariant?

### 16.3 Byzantine-resilient observability

Develop observability conditions under adversarial sensors, reports, logs, links, and inference engines. The target should not be omniscience but certified sufficiency for safe action.

Question: Which dangerous distinctions must become observable before recoverability is lost?

### 16.4 Certified inference and diagnosis

Define \(B_t\) and \(H_t\) objects with soundness, freshness, and usefulness guarantees. Include ambiguity sets, diagnosis sets, causal hypothesis sets, and proof-carrying estimates.

Question: What should the system agree on when it cannot safely agree on a single state or single cause?

### 16.5 Capability estimation

Treat capability as partially observed state. Develop upper and lower capability bounds, evidence rules for updating them, and interventions that shrink or compensate for unsafe capability envelopes.

Question: When is “node removed” equivalent to “invariant-relevant capabilities removed or bounded”? Usually it is not.

### 16.6 Robust action under ambiguity

Synthesize actions safe over \(B_t\) and \(H_t\), including actions that probe before acting, degrade service, reconfigure topology, or preserve a weaker invariant level.

Question: What is the right analogue of a controlled predecessor when the state is certified only as an ambiguity object?

### 16.7 Actuation semantics

Specify how commands become transitions. Include actuator faults, bypasses, delays, partial execution, over-execution, nonexecution, and evidence of effect.

Question: When does agreement over an intervention become control over the generalized state?

### 16.8 Fault-domain separability

Develop a theory of common-mode Byzantine dependence. Define when component contracts can be composed without silently sharing root keys, software stacks, models, operators, incentives, or physical supports.

Question: When is replication actually diversity?

### 16.9 Disturbance algebra

Generalize from a single Byzantine fault bound to typed disturbance classes with explicit composition rules. Include malice, bugs, edge cases, model error, environment shifts, strategic behavior, and common-mode accidents.

Question: What disturbance classes can be composed additively, and which invalidate one another’s assumptions?

### 16.10 Recovery, adaptation, and moving assumptions

Study mobile faults, adaptive adversaries, component rejuvenation, model updates, topology changes, evidence decay, and changing invariants.

Question: Does the controller preserve the invariant under a changing system, or only under a frozen snapshot?

---

## 17. Minimal benchmark ladder

The benchmark program should add one difficulty at a time. Each level should preserve enough continuity with the previous level that the failing assumption is visible.

| Level | Controlled object | New difficulty | Expected obstruction |
|---|---|---|---|
| \(L_0\) | replicated symbolic register | ordinary BFT agreement | consensus and liveness assumptions |
| \(L_1\) | replicated state plus trusted external sensor | external state is observed but not adversarially | abstraction and timing |
| \(L_2\) | external state with Byzantine sensors | state must be inferred | observability and certified inference |
| \(L_3\) | external state with uncertain diagnosis | same observation has multiple causes | agreement on disagreement and probing |
| \(L_4\) | external state with Byzantine actuators | commands may not become transitions | actuation contracts and verification |
| \(L_5\) | dynamic capabilities | actors retain or lose hidden action channels | capability inference and mediation |
| \(L_6\) | multiple fault domains | components share causes | decoupling and common-mode dependence |
| \(L_7\) | recovery and adaptation | repaired, replaced, or mobile components | persistence of guarantees over changing assumptions |

At every level, require a shortest counterexample in which the previous level’s theorem no longer holds. Then add the weakest condition that blocks that counterexample.

---

## 18. Minimal examples to keep the theory honest

### 18.1 Replicated counter

A replicated counter with BFT consensus is the base case. The invariant is a data invariant such as nonnegative balance. The state, transition rule, and evidence are mostly protocol-internal.

Question: What exactly is “controlled” here: agreement, trace validity, data state, or authorization to update?

### 18.2 Counter with external custody

Now let the counter represent a resource that can also be moved through an off-ledger custodian. The ledger may remain BFT-correct while the resource invariant fails.

Question: Is the off-ledger transition part of \(X\), part of \(\widetilde W\), mediated by \(\widetilde U\), or excluded as a trusted assumption?

### 18.3 Sensorized physical variable

Let the invariant be \(p\le p_{max}\). The controllers observe sensors, infer \(B_t\), and command valves. The central issue is whether the correct controllers can maintain a pressure envelope and actuate before escape.

Question: Which failures are observational, inferential, temporal, or actuator-level?

### 18.4 Capability-removal example

A node is removed from protocol membership but retains an actuator credential, a physical bypass, or an administrative channel. The base BFT system records removal; the generalized system may still be unsafe.

Question: What evidence establishes that removal changed the capability envelope enough to matter?

### 18.5 Diagnostic ambiguity example

A bad pressure reading may mean sensor attack, actuator failure, environment shift, or model error. The safe action may be to probe rather than punish or shut down.

Question: How does the controller choose actions over \((B_t,H_t)\) without needing premature attribution?

---

## 19. Relation to existing work

This agenda is a synthesis problem, not a claim that all parts are new.

Byzantine agreement and practical BFT provide the base theory of agreement and replicated execution under arbitrary faulty behavior. State-machine replication gives a particularly clean setting because the object controlled by agreement is largely internal to the protocol.

Resilient and secure state-estimation work already studies estimation under adversarial sensors and Byzantine nodes. That literature should be treated as central, not auxiliary, because generalized invariant control cannot act on a state that it cannot soundly infer.

Control-barrier functions, controlled invariance, viability theory, runtime assurance, Simplex architectures, distributed Simplex, shield synthesis, supervisory control under attacks, resilient consensus with constraints, and assume–guarantee reasoning are all adjacent. They each control or certify one part of the loop. The proposed research problem asks how to connect those parts without hiding unproved assumptions at their interfaces.

The possible novelty is not “BFT plus control” in a slogan sense. The possible novelty is a disciplined lifting theory: starting with BFT as control over a restricted object, enlarging the state, and classifying the additional observation, inference, diagnosis, capability, actuation, timing, decoupling, and recovery conditions required for the lift.

This novelty claim is deliberately weak. A literature review may find close antecedents in cyber-physical security, supervisory control, distributed estimation, formal methods, institutional multi-agent systems, runtime enforcement, or capability security. The note should therefore be used to ask better search questions, not to assert priority.

---

## 20. How to use this note as a research instrument

When applying this note to a candidate system or when continuing the theory, proceed as follows.

First, identify the base BFT object. Say whether BFT is being reconstructed as control over an agreement relation, trace language, replicated state, epistemic certificate structure, or something else. Do not proceed until the base object is explicit.

Second, define the proposed extension \(p:X\to S\) and the generalized invariant \(\widetilde K\subseteq X\). State why \(\widetilde K\) does not already factor through the base state. If it does factor through the base state, the generalization may be unnecessary.

Third, identify the control-relevant abstraction \(\alpha:X\to Z\). Avoid demanding complete state knowledge if a smaller certified abstraction suffices. Conversely, do not omit variables that can change safe action sets.

Fourth, specify the closed-loop stack \(X\to O\to E\to B,H\to D\to U\to X'\to O'\). For each arrow, state the fault model, timing bound, evidence rule, and contract. If an arrow is trusted, mark it as trusted rather than proving around it.

Fifth, construct the certified information object. The target is not “the state is \(x\),” unless justified. Prefer a sound envelope \(x_t\in B_t\), a control-relevant abstraction \(z_t\in C_t\), and a hypothesis set \(H_t\) when diagnosis matters.

Sixth, state the robust action condition. The action must be safe for all states and hypotheses still live, or the controller must choose a probing or degrading action that preserves recoverability.

Seventh, check actuation and verification. A certificate is not an effect. A command is not a transition. A receipt is not necessarily truth. Specify how the resulting state is known, bounded, or assumption-bounded.

Eighth, check fault-domain separability. List common causes across modules: software, model, operator, root key, clock, supply chain, physical co-location, economic incentive, data source, governance process. Do not count correlated components as independent.

Ninth, classify lift failures. Use the taxonomy in Section 15 and find the shortest counterexample in which consensus succeeds but the generalized invariant fails.

Tenth, weaken or strengthen the claim. If the full invariant cannot be guaranteed, identify whether a smaller invariant, a smaller state extension, a stronger mediation assumption, a different abstraction, or a probabilistic guarantee is the honest result.

This section is not a separate prompt. It is the operating protocol of the note.

---

## 21. Compact glossary

**Base BFT object.** The restricted object controlled by the original BFT formulation: replicated state, agreement relation, trace language, or epistemic commitment structure.

**State-space lift.** A proposed extension from base object \(S\) to generalized state \(X\), usually with projection \(p:X\to S\).

**Control-relevant abstraction.** A map \(\alpha:X\to Z\) retaining the distinctions needed for invariant truth and safe action selection.

**Certified information state.** An object \(B_t\), \(C_t\), or certificate bundle that soundly contains the true state or abstraction under stated assumptions.

**Agreement on disagreement.** Consensus not on a single state or cause, but on the set of remaining possible states, diagnoses, or capabilities.

**Capability envelope.** A certified upper or lower bound on what an actor can cause or influence.

**Effective exclusion.** A condition under which an actor’s remaining invariant-relevant capabilities are removed, bounded, or compensated for; not merely removal from protocol membership.

**Disturbance algebra.** A typed model of adversarial, buggy, environmental, strategic, and edge-case disturbances, including composition and common-mode exclusions.

**Fault-domain separability.** The condition under which subsystem fault assumptions compose without hidden common causes.

**Lift failure.** A counterexample showing that a guarantee over the base BFT object does not extend to the generalized state.

---

## 22. Reference pointers

The following sources are useful anchors, not a finished bibliography.

- Lamport, Shostak, and Pease, “The Byzantine Generals Problem,” ACM TOPLAS, 1982.
- Castro and Liskov, “Practical Byzantine Fault Tolerance,” OSDI, 1999.
- Mitra and Sundaram, “Byzantine-Resilient Distributed Observers for LTI Systems,” Automatica, 2019.
- Shoukry, Nuzzo, Puggelli, Sangiovanni-Vincentelli, Seshia, and Tabuada, “Secure State Estimation for Cyber Physical Systems under Sensor Attacks,” IEEE TAC, 2017.
- Ames, Xu, Grizzle, and Tabuada, “Control Barrier Function Based Quadratic Programs for Safety Critical Systems,” IEEE TAC, 2017.
- Seto, Krogh, Sha, and Chutinan, “The Simplex Architecture for Safe Online Control System Upgrades,” ACC, 1998.
- Mehmood, Stoller, Grosu, Roy, Damare, and Smolka, “A Distributed Simplex Architecture for Multi-Agent Systems,” SETTA, 2021.
- Bloem, Könighofer, Könighofer, and Wang, “Shield Synthesis: Runtime Enforcement for Reactive Systems,” TACAS, 2015.
- Wang, Mou, and Sundaram, “Resilience for Distributed Consensus with Constraints,” arXiv, 2022 / later IEEE TAC.
