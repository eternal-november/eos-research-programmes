# From Byzantine Fault Tolerance to Control of Generalized State
## A provisional research note and working instrument

**Working name:** distributed invariant control, or Byzantine-resilient distributed control. Neither name should be treated as settled.

## Purpose

This note states a research problem and specifies a way to work on it. It is intended to be used directly: continue the investigation by refining its definitions, constructing counterexamples, locating prior work, and replacing broad conditions with the weakest conditions that support actual results. Do not treat the formulations below as a completed theory, and do not preserve them merely because they appear in this document.

The task is:

> **Formulate Byzantine fault tolerance as a control problem, then characterize the conditions under which the controlled state—or, if necessary, the controlled trace or information object—can be generalized.**

The motivating intuition is that ordinary BFT controls a relatively narrow object: committed protocol state, an agreement relation, or an admissible execution language. The proposed generalization asks whether the same basic idea can apply when the relevant state includes variables that are sensed, inferred, physically or institutionally mediated, only partially observed, or controlled through components that may themselves be Byzantine.

The problem should not be reduced in advance to “BFT plus coercion,” “a ledger plus actuators,” or any particular institutional architecture. Those may be realizations of some cases. The prior question is what makes a state extension controllable at all.

---

## 1. The research question

Let a base BFT system maintain some property over a controlled object \(S\). The simplest state-space picture is

\[
\Sigma_0=(S,A,W,T,\{O_i\}_{i\in N},\Phi),
\]

where \(S\) is state, \(A\) is the joint action space, \(W\) is the admissible fault and disturbance class, \(T\) is the transition relation, \(O_i\) is the local observation available to process \(i\), and \(\Phi\) is a safety, agreement, validity, or progress specification. A distributed policy maps local histories to actions.

Now consider a richer system

\[
\Sigma_1=(X,\widetilde A,\widetilde W,\widetilde T,
\{\widetilde O_i\}_{i\in N},\widetilde\Phi),
\]

where \(X\) includes additional state relevant to the desired guarantee. The base and extended systems may be connected by a projection \(p:X\to S\), but a relation

\[
R\subseteq X\times S
\]

is often more appropriate: a single protocol state may be compatible with several world states, and a single world state may admit several protocol representations.

The central problem is:

> **For which extensions \((\Sigma_0,R,\Sigma_1)\) does there exist a Byzantine-resilient distributed policy on \(X\) that preserves \(\widetilde\Phi\), remains meaningfully related to the base BFT behavior, and satisfies its timing and service requirements?**

Call such an extension **liftable** for now. This is only a working term. A useful definition of liftability will probably need to include:

1. **Property preservation:** every admissible extended execution satisfies the specified safety property, and any liveness claim is stated under its required synchrony and availability assumptions.
2. **Refinement or realization:** the extended execution remains related to an admissible base execution, rather than merely preserving an unrelated invariant.
3. **Distributed implementability:** the policy uses only permitted local histories, communication, and actions.
4. **Non-vacuity:** the guarantee is not obtained solely by disabling the system unless shutdown is itself the specified safe behavior.

These clauses should be challenged. A trace-based or epistemic formulation may prove cleaner than a state-space one. The first research task is therefore not to defend this tuple notation; it is to determine which reconstruction of BFT exposes the right structure for generalization.

---

## 2. In what sense is BFT already control?

At least three reconstructions deserve separate treatment.

### 2.1 State or set invariance

Let \(q_i\) be the state of replica \(i\). A protocol may be viewed as keeping the committed states of correct replicas within an agreement relation such as

\[
\Delta_H=\{(q_1,\ldots,q_n):q_i=q_j
\text{ for all correct }i,j\},
\]

or within a more refined set expressing agreement, validity, and monotonic extension. This resembles robust distributed set invariance under adversarial inputs.

The analogy is imperfect. Protocol implementations can contain tentative, divergent, or view-local state while preserving safety at the level of decisions or commits. A state-invariance account may therefore require an augmented state that records histories, certificates, or automaton state.

### 2.2 Trace restriction

BFT safety is often more naturally expressed as a restriction on executions:

\[
\operatorname{Trace}(P,W_f)\subseteq L_{\mathrm{safe}}.
\]

Safety is prefix-closed; liveness constrains infinite executions under additional assumptions. This places BFT near supervisory control and reactive synthesis: the protocol restricts the language of possible system behavior despite uncontrollable or adversarial events.

### 2.3 Epistemic or decisional control

A BFT protocol also controls when a correct process is permitted to move from uncertainty to an irreversible decision. Quorums, signatures, timeouts, and certificates transform local histories into justified actions. The controlled object may therefore be an information state, a knowledge condition, or a set of admissible decisions rather than a physical state vector.

These views may be equivalent after suitable augmentation, or they may expose genuinely different generalizations. Do not choose among them by taste. Compare them on the same examples and ask which distinctions each one preserves or erases.

Agreement is itself relational across replicas, and some relevant security properties are trace properties or hyperproperties rather than ordinary predicates on a single instantaneous state. A state-space formulation may encode them by taking a product with monitors, histories, or multiple executions, but the encoding should be exhibited rather than assumed harmless. The project concerns generalization of the controlled object, not a commitment that every useful specification must look like a conventional state invariant.

### 2.4 The constitutive peculiarity of protocol state

Many BFT systems operate on state that is partly **constituted by the protocol itself**. Once a transaction is validly committed, that commitment helps make the replicated state what it is. Within the model, there may be little distance between:

\[
\text{agreement on a transition}
\quad\text{and}\quad
\text{the transition of the controlled state}.
\]

That coincidence weakens as the state is generalized. It is useful to classify each added variable by how it relates to protocol decisions:

| Variable class | Relation to agreement | Example | Main additional burden |
|---|---|---|---|
| **Protocol-constituted** | A valid protocol transition makes the value true within the system model | committed log position, replicated balance | agreement, validity, execution consistency |
| **Reliably mediated** | A protocol decision causes a state change through an interface whose behavior is assumed or verified | credential revocation, an interlocked digital actuator | authority, actuation semantics, latency, bypass resistance |
| **Observed or autonomous** | The variable evolves independently; the protocol can only sense and influence it | pressure, possession, human behavior, external market state | observability, inference, robust control, verification |
| **Mixed** | Some transitions are constituted or mediated and others occur outside the protocol | custody, organizational authority, hybrid cyber-physical resources | explicit boundary and realization model |

This classification is not an ontology of everything that must be placed in \(X\). It is a diagnostic: an extension acquires additional proof obligations when agreement no longer constitutes the variables being controlled.

---

## 3. Let the invariant determine the state

“Generalized state” should not become a list of everything in the universe. For a proposed property \(K\), identify the smallest control-relevant abstraction that can support the claim.

Let the concrete state be \(x\in X\) and let

\[
\alpha:X\to Z
\]

be a candidate control abstraction. The controller need not recover all of \(x\). It needs certified information about \(z=\alpha(x)\) sufficient to select safe actions.

A basic adequacy test is:

\[
\alpha(x)=\alpha(x')
\quad\Longrightarrow\quad
U_{\mathrm{safe}}(x)\cap U_{\mathrm{safe}}(x')\neq\varnothing
\]

for states that the controller may have to handle under the same information history. If two concrete states collapse to the same abstraction but require incompatible actions, the abstraction is too coarse for the intended guarantee.

The invariant itself may concern different kinds of truth-makers:

| Target property | What makes it true or false | Typical missing interface |
|---|---|---|
| protocol consistency | message, certificate, and commit history | agreement and authentication |
| application-data integrity | application transition semantics | validation and deterministic execution |
| physical safety | material dynamics | sensing, estimation, actuation |
| capability restriction | actual available action channels | mediation, testing, revocation, containment |
| authority | credentials and institutional rules as actually enforced | identity, delegation, jurisdiction, execution |
| service continuity | resources, topology, and functioning components | redundancy, reconfiguration, recovery |
| epistemic sufficiency | relationship between evidence, belief, and actual state | resilient inference and model validity |

Do not assume these properties can be combined without changing the model. A proof about a protocol invariant may be silent about a physical or capability invariant even when the same names appear in both.

A useful audit rule is:

> **Every variable used by the controller must be directly controlled, soundly inferred, or bounded by an explicit assumption.**

This is not a theorem. It is a way to expose hidden trust. If a design uses “current state,” “available capability,” “independent sensors,” “valid model,” “obedient actuator,” or “bounded adversary,” identify the mechanism or assumption that licenses that variable.

Also distinguish the form of the objective. Forward invariance from an initially admissible state, recovery after a violation, bounded damage during recovery, and continued service are different problems. A construction that proves one should not inherit the language of the others without an explicit reduction.

### 3.1 Capability as a possible state variable

Capability is important when the invariant depends on what an actor can cause, but it should not be made foundational in every domain. Distinguish at least:

\[
C_i^{\mathrm{declared}},\qquad
C_i^{\mathrm{certified}},\qquad
C_i^{\mathrm{real}}.
\]

A conservative controller may maintain an upper bound

\[
C_i^{\mathrm{real}}\subseteq \widehat C_i,
\]

because underestimating a Byzantine actor's capability is dangerous. Revocation, isolation, rate limits, interlocks, custody changes, or physical intervention are then candidate ways to shrink the real or certified capability envelope. They are not assumed primitives of the theory.

---

## 4. The generalized loop includes sensing and inference

A useful, non-canonical decomposition is

\[
x_t\longrightarrow o_t\longrightarrow e_t
\longrightarrow (B_t,H_t)\longrightarrow d_t
\longrightarrow u_t\longrightarrow x_{t+1}
\longrightarrow o_{t+1}.
\]

Here:

- \(x_t\) is the concrete state;
- \(o_t\) is raw observation;
- \(e_t\) is evidence after authentication, provenance checks, freshness checks, and other admissibility rules;
- \(B_t\) is a certified information object, often an ambiguity set over control-relevant state;
- \(H_t\) is a set of remaining fault, causal, or model hypotheses when diagnosis matters;
- \(d_t\) is a coordinated decision or policy selection;
- \(u_t\) is the action presented to the relevant effectors;
- the final arrow verifies what the action actually changed.

The decomposition should be changed when a domain requires it. Its purpose is to prevent agreement, truth, authorization, and effect from being silently identified.

### 4.1 Byzantine-resilient observability

The ordinary observability question becomes adversarial and distributed:

> Can the correct controllers distinguish states that require incompatible actions despite corrupt sensors, reporters, links, logs, estimators, stale information, and model error—and can they do so before recoverability is lost?

A basic impossibility pattern is as follows. Let \(x,x'\) be two states such that

\[
U_{\mathrm{safe}}(x)\cap U_{\mathrm{safe}}(x')=\varnothing.
\]

If an admissible adversary can produce identical correct-controller observation histories from \(x\) and \(x'\) until the action deadline, then no observation-based distributed policy can guarantee safety from both states. This is the control analogue of an indistinguishability argument.

A positive result should therefore connect measurement structure, communication structure, fault placement, and time to a distinguishability condition. Existing work on Byzantine-resilient distributed observers already gives nontrivial examples of such conditions for linear systems; the general research problem is broader.[4]

### 4.2 Certified information states

The controller generally should not be assumed to know a point state. Let

\[
B_t\subseteq Z
\]

be an ambiguity set or other certificate-bearing information object with the soundness condition

\[
z_t=\alpha(x_t)\in B_t
\]

under stated assumptions. A robust action satisfies

\[
u_t\in U_{\mathrm{safe}}(B_t)
:=\bigcap_{z\in B_t}U_{\mathrm{safe}}(z).
\]

If this intersection is empty, consensus has not failed; the epistemic-control interface has failed. The system may need to gather information, enter a conservative mode, relax a lower-priority objective, or accept that the state is outside its recoverable set.

Do not assume all correct controllers need identical point estimates. Depending on the problem, the minimal coordination object could be:

- agreement on which reports were received;
- agreement on an admissible evidence set;
- compatible local ambiguity sets;
- agreement on a joint ambiguity set;
- agreement on a diagnosis set;
- agreement only on an action certificate showing that a proposed action is safe for every state still possible.

One research question is whether generalized control sometimes requires *less* global consensus than state-machine replication, provided local beliefs and actions satisfy compatible contracts.

### 4.3 Diagnosis and epistemic actions

Knowing that the state is dangerous is not the same as knowing why. Different hypotheses—sensor attack, actuator failure, model shift, controller compromise, or environmental disturbance—may produce similar evidence but imply different interventions.

The action model may therefore need to distinguish:

\[
U=U_{\mathrm{observe}}\cup U_{\mathrm{probe}}
\cup U_{\mathrm{decide}}\cup U_{\mathrm{actuate}}
\cup U_{\mathrm{reconfigure}}\cup U_{\mathrm{recover}}.
\]

Some actions are epistemic: challenge a sensor, request fresh attestation, inject a safe test signal, compare an independent channel, delay commitment, or perform a controlled failover to distinguish hypotheses. This creates a dual-control problem. Estimation and control may not separate cleanly because actions change both the world and what can be learned about it.

---

## 5. Fault structure, decoupling, and composition

A single statement such as “at most \(f\) Byzantine nodes” is often too coarse once the loop is generalized. The location and dependence of faults matter.

| Interface | Representative failures or attacks | Required specification |
|---|---|---|
| \(x\to o\) | blind spots, spoofing, drift, occlusion, adversarial environment | measurement relation and physical assumptions |
| \(o\to e\) | forgery, replay, log tampering, selective reporting | authentication, provenance, freshness, admissibility |
| \(e\to B,H\) | poisoned model, correlated sensor error, invalid abstraction, buggy inference | estimator soundness and model class |
| \(B,H\to d\) | equivocation, quorum failure, inconsistent local beliefs, timing failure | coordination and decision semantics |
| \(d\to u\) | invalid delegation, confused deputy, stale authority, privilege escalation | authorization and scope semantics |
| \(u\to x'\) | compromised actuator, ignored command, delay, saturation, bypass | actuation relation and fault budget |
| \(x'\to o'\) | fabricated receipt, unverifiable effect, delayed feedback | post-action verification |
| cross-layer | shared code, root key, vendor, clock, operator, site, model, training data, incentive | common-cause and dependency model |

“Byzantine” remains useful as a behavioral envelope—arbitrary deviation—but it does not by itself specify where arbitrary behavior may occur or which nominal replicas share one failure cause. Nor should malicious faults, accidental bugs, environmental disturbances, model error, and strategic but protocol-conforming behavior be collapsed automatically into one adversary class. They may support different bounds, evidence, and composition rules even when a worst-case analysis later takes their union.

### 5.1 Decoupling is conditional, not absolute

Subsystems should be separated enough to contain faults and permit local analysis, but coupled enough to preserve observability, controllability, and coordination. The design objective is not simply “more decoupling.” It is to reduce paths of common failure while retaining the paths needed for the control proof.

Represent at least the following relations separately when they differ:

\[
G_{\mathrm{physical}},\quad
G_{\mathrm{sensing}},\quad
G_{\mathrm{communication}},\quad
G_{\mathrm{decision}},\quad
G_{\mathrm{authority}},\quad
G_{\mathrm{actuation}},\quad
G_{\mathrm{fault}}.
\]

A component boundary in one graph does not imply a fault-containment boundary in another. Two sensors implemented by the same stack, operated by the same organization, and calibrated from the same reference may be two nodes but one fault domain.

### 5.2 Adversarial assume–guarantee contracts

A subsystem contract may need more than an assumption and a guarantee. A working form is

\[
\mathcal C_j=(A_j,G_j,F_j,\tau_j,D_j),
\]

where \(F_j\) states the tolerated fault class, \(\tau_j\) states timing and freshness bounds, and \(D_j\) records dependencies or common-cause exclusions.

For example, a sensing contract might guarantee

\[
x_t\in B_t,
\qquad
\operatorname{diam}(B_t)\le \varepsilon,
\qquad
\text{age}(B_t)\le \tau,
\]

provided a specified number and arrangement of sensors are correct. A control contract can consume that guarantee only if its assumptions are actually entailed. An actuation contract must then bound the realized post-state, not merely acknowledge receipt of a command.

Composition requires at least:

1. upstream guarantees imply downstream assumptions;
2. timing budgets compose within the recoverability horizon;
3. the fault and dependency assumptions are jointly satisfiable;
4. a single common cause is not counted as several independent tolerated faults;
5. local invariants imply the intended global property under the coupling model.

Existing assume–guarantee work on compositional set invariance supplies one starting point, but adversarial dependence, Byzantine interfaces, and changing fault domains remain central additions rather than minor annotations.[5]

### 5.3 Is there an adversarial separation principle?

Classical estimation and control can sometimes be designed separately. The generalized problem should ask when a comparable separation is valid:

> Under what conditions can a Byzantine-resilient estimator, a BFT decision layer, and a robust controller be synthesized independently and then composed?

Reasons separation may fail include active sensing, adaptive adversaries, action-dependent observations, shared fault domains, model uncertainty, and controllers whose interventions change membership or capability. Establishing a useful restricted separation theorem—or a sharp impossibility result—would be a substantive contribution.


### 5.4 Reflexivity and the assumption boundary

The estimator, agreement mechanism, controller, contract monitor, and recovery logic are themselves components with state and failure modes. Enlarging the controlled object can therefore make the assurance argument recursive. The recursion does not have to continue indefinitely, but it must end visibly: in a trusted primitive, a bounded fault assumption, a physical constraint, a diversity claim, or a weaker property that survives failure of the assurance layer.

For each proposed theorem, identify which mechanisms are inside the adversary model, which are modeled only by contracts, and which remain trusted. Moving a component into \(X\) is not automatically an improvement if its own observation and actuation assumptions are then left implicit.

---

## 6. Actions, actuation, and effective influence

Consensus is one action-producing mechanism, not the whole control loop. The generalized action model should state what interventions can change and through which causal interface.

Useful action families include:

- observation and probing;
- filtering, certification, and commitment;
- ordinary plant or application control;
- authority or credential changes;
- routing, topology, and membership reconfiguration;
- quarantine, rate limitation, or isolation;
- substitution and failover;
- repair, recovery, and reintegration;
- verification of effects.

Do not infer from this list that every domain needs every action. Determine which actions are necessary by computing or characterizing the safe predecessor of the target set under the actual transition model.

A system may need to reduce an actor's capability when that actor retains an action that can destroy recoverability. In some domains this is cryptographic revocation; in others it is a hardware interlock, custody change, network isolation, or physical enforcement. “Police” is therefore a possible implementation of an actuator at one boundary, not the general abstraction.

Keep the following distinctions explicit:

\[
\text{detection}\neq\text{attribution}
\neq\text{containment}\neq\text{punishment}.
\]

Invariant preservation may require containment without reliable attribution, and it need not require punishment. Conversely, punishment after the fact may do nothing to preserve the invariant.

Logical removal from a BFT membership set is likewise not automatically effective removal from the generalized system. Whether it is sufficient depends on which state transitions the removed actor can still cause and whether the remaining system retains adequate sensing, decision, and actuation capacity.

---

## 7. A taxonomy of lift failures

Organize the research around failed extensions. The categories below are prompts for counterexamples, not an assertion that they are complete or independent.

| Failure | Formal symptom | Question to answer |
|---|---|---|
| **representation** | the chosen abstraction merges states with incompatible safe actions | What is the coarsest control-sufficient abstraction? |
| **observability** | dangerous states remain indistinguishable to correct controllers | What sensing and communication redundancy forces timely distinction? |
| **inference** | evidence does not support a sound, useful ambiguity set | Which estimator guarantees survive Byzantine reports and model error? |
| **diagnosis** | the state is bounded but causal hypotheses require incompatible interventions | Can a safe probe separate the hypotheses before the deadline? |
| **coordination** | correct controllers cannot obtain compatible beliefs or actions | What is the minimal object that must be agreed upon? |
| **viability or controllability** | no admissible action keeps every possible state within the target set | Was information too weak, action authority too small, or the response too late? |
| **actuation** | certified commands do not bound the realized transition | Which interfaces must be mediated, replicated, interlocked, or assumption-bounded? |
| **semantic realization** | protocol state remains internally consistent while losing its intended relation to external state | What maintains the relation \(R\) between representation and world? |
| **timing and resources** | estimation, agreement, or actuation exceeds the recoverability margin or exhausts capacity | What are the correct delay, freshness, bandwidth, energy, and spare-capacity conditions? |
| **dependency** | local fault assumptions are invalidated by a shared cause | How should common-mode Byzantine dependence be represented and bounded? |
| **verification** | the effect of intervention cannot be distinguished from nonexecution or deception | What closes the feedback loop? |
| **recovery and evolution** | repair, reconfiguration, mobile faults, or model drift invalidate the prior guarantee | Which properties must be maintained across changing topology and assumptions? |
| **specification** | the invariant omits the actual harm, conflicts with other requirements, or is not operational | What concrete state or trace makes the specification true? |

The point of the taxonomy is not to name many things. It is to prevent a positive result at one interface from being mistaken for a system-level result.

---

## 8. Candidate result forms

The following are theorem and counterexample templates. They are not established claims about the full problem.

### 8.1 BFT-to-control reconstruction

Give a precise mapping from a standard BFT specification to an adversarial control or safety-game formulation. State exactly which protocol variables must be included for safety to become invariant, and how liveness assumptions appear in the game.

A successful reconstruction should illuminate rather than merely rename consensus.

### 8.2 Indistinguishability impossibility

If two admissible states generate the same correct-controller histories through the last safe decision time and require disjoint safe actions, no distributed observation-based policy preserves the invariant from both.

Prove this for the weakest useful model, then determine how authentication, trusted observations, active probes, or extra time remove the obstruction.

### 8.3 Estimator–controller composition

Let a resilient estimator produce \(B_t\) such that

\[
z_t\in B_t.
\]

Let the selected action satisfy

\[
\operatorname{Post}(B_t,u_t,W_t)\subseteq K.
\]

Under a valid actuation model, the next state lies in \(K\). The elementary implication is immediate; the actual research is to state distributed, temporal, recursive conditions under which the estimator guarantee, action certificate, and actuation guarantee remain valid at every step.

The belief-set dynamics may themselves be the controlled system.

### 8.4 Unmediated-transition impossibility

If an admissible Byzantine actor can force a transition outside \(K\) before any correct action can block or compensate for it, then no informational agreement protocol can guarantee \(K\) from that state.

This should be formulated without assuming that the missing mechanism is coercion. The obstruction is absence of timely causal influence.

### 8.5 Compositional lift theorem

Identify conditions under which local resilient estimators, local invariant controllers, a BFT coordination mechanism, and actuator contracts compose into a global invariant. The theorem must account for coupling, correlated faults, timing, and changes in topology or role assignment.

A corresponding counterexample should show how naïve assume–guarantee composition double-counts independence.

### 8.6 Minimal coordination theorem

Determine when agreement on a common state estimate is unnecessary. It may suffice that local beliefs have a nonempty common safe-action set, or that a common action certificate is valid despite differing local beliefs.

This line could reveal that the relevant generalization is not “more consensus” but a different interface between distributed inference and control.

### 8.7 Adversarial separation theorem or failure

Find conditions under which estimation, agreement, and control can be synthesized separately. Where those conditions fail, construct a minimal example in which each module is correct under its local contract but their composition is unsafe because the adversary couples the modules.

For every proposed result, first search for the smallest counterexample. Record whether the failure is mathematical, architectural, or merely a consequence of an unnecessarily strong formulation.

---

## 9. Working procedure

Apply the following procedure to one state extension at a time. The procedure is part of the research note, not an appendix to be translated into separate instructions.

### Step 1: Choose a base BFT object

State exactly what is being controlled: committed state, agreement relation, trace language, certificate state, or something else. Write the safety and liveness properties without using the word “consensus” as a substitute for them.

### Step 2: Reconstruct it as control

Specify state or trace, local information, admissible Byzantine behavior, controllable actions, uncontrollable events, and the winning condition. Note any protocol facts that become trusted plant assumptions in the control model.

### Step 3: Add one state dimension or one interface

Do not begin with a complete cyber-physical-institutional system. Add one external variable, one uncertain sensor channel, one compromised actuator, one changing capability, or one subsystem boundary. Define the relation \(R\) to the base system.

### Step 4: State the target property and its truth-maker

Say what concrete facts make the property true. Separate safety from liveness, service, recovery, and epistemic objectives. Identify conflicts or priority rules rather than silently conjoining incompatible goals.

### Step 5: Find a control-sufficient abstraction

Propose \(\alpha:X\to Z\). Test it by searching for states with the same abstraction and incompatible safe actions. Prefer certified sufficiency to complete state reconstruction.

### Step 6: Specify evidence and inference

Define observations, provenance, freshness, the fault model for sensors and estimators, and the information object \(B_t\) or \((B_t,H_t)\). State soundness, tightness, and latency separately.

### Step 7: Specify fault domains and dependencies

Partition faults by interface only when justified. Record shared implementations, operators, roots of trust, models, clocks, locations, and incentives. Use a joint adversary model or dependency hypergraph rather than assuming an independent product distribution or independent fault budget.

### Step 8: Identify the minimal coordination object

Ask whether correct controllers need agreement on reports, evidence, beliefs, diagnoses, actions, or only safety certificates. Avoid introducing global consensus where compatible local control contracts would suffice.

### Step 9: Define the full action and actuation semantics

Include epistemic actions, ordinary control, reconfiguration, recovery, and verification where relevant. Distinguish an authorized command from its realized effect. State delays, saturation, bypasses, and remaining adversarial capabilities.

### Step 10: Compute or characterize recoverability

Determine the set of beliefs or states from which a safe action exists under the fault model and timing constraints. If no safe action exists, identify whether probing, fallback, reconfiguration, or a weaker property restores viability.

### Step 11: Attempt compositional proof

Write contracts for each subsystem and check assumptions against upstream guarantees. Audit common-mode dependencies and total timing. Do not claim global invariance from local invariants without an explicit coupling argument.

### Step 12: Produce the smallest failure trace

Construct an execution in which the base BFT mechanism succeeds but the generalized property fails. Then change one assumption or mechanism at a time until the lift succeeds. This differential analysis is more informative than proposing a large architecture at the outset.

Each completed pass should yield:

- a formal model with a visible assumption boundary;
- one proposed lift or non-lift result;
- one minimal counterexample;
- one small executable or model-checkable benchmark;
- a list of assumptions whose weakening changes the result;
- a precise statement of what remains unmodeled.

---

## 10. Minimal benchmark sequence

Use examples that break one favorable BFT coincidence at a time.

### A. Protocol-constituted register

Start with a replicated register or counter. The protocol determines valid transitions and committed state. Show exactly how its safety property becomes a control invariant or trace restriction.

### B. One external variable with trusted interfaces

Add a binary or scalar variable \(x\) whose value is sensed and changed through trusted channels. The BFT layer agrees on observations and commands. Determine what new assumptions enter even before any interface is Byzantine.

### C. Byzantine sensing

Allow a bounded set of observation channels or reporters to send arbitrary histories. Compare point estimation, interval or ambiguity-set estimation, and action certification. Derive an indistinguishability counterexample and a positive redundancy condition.

### D. Byzantine actuation

Allow commanded and realized actions to differ. Specify whether effectors are replicated, threshold-controlled, monitored, or partly uncontrollable. Identify the robust predecessor set under the actuator fault model.

### E. Active diagnosis

Introduce two hidden fault hypotheses that require different actions. Add a safe probing action and determine when information gathering preserves recoverability.

### F. Dynamic capability or membership

Allow actions to change who can observe, decide, or actuate. Distinguish protocol membership from real capability. Test whether reconfiguration preserves both safety and residual control capacity.

### G. Two composed subsystems with a shared cause

Give each subsystem a locally valid contract, then introduce a hidden common dependency. Use the example to test fault-domain annotations and compositional reasoning.

A finite-state partially observed safety game is one plausible first formalism for this sequence because it makes information, actions, adversarial choices, and synthesis explicit. Its adequacy should be tested rather than presumed. Continuous, stochastic, hybrid, institutional, or game-theoretic models become necessary when the finite model erases a phenomenon on which the claim depends.

---

## 11. Adjacent work and the unresolved research boundary

The proposed program sits across several mature literatures. A novelty claim should be made only after comparing the exact formal objects and trust boundaries.

- **Byzantine agreement and state-machine replication** provide the base models of arbitrary process behavior, agreement, validity, ordering, and replicated execution.[1–3]
- **Byzantine-resilient distributed estimation and observers** already study when a network of sensors can reconstruct dynamical state despite compromised nodes, including graph and measurement redundancy conditions.[4]
- **Resilient consensus and constrained multi-agent control** connect Byzantine filtering, topology, state constraints, and convergence.[6]
- **Assume–guarantee control and compositional invariance** provide machinery for decomposing networked safety proofs into subsystem contracts.[5]
- **Supervisory control under sensor and actuator attacks** explicitly models adversarial rewriting of observed and commanded events and synthesizes resilient supervisors.[7]
- **Runtime enforcement, shields, and Simplex-style assurance** study mechanisms that monitor or override an untrusted controller to preserve selected safety properties.[8–10]
- **Byzantine fault detection, proactive recovery, and fault-containment architecture** address detection, repair, rejuvenation, and architectural separation beyond pure fault masking.[11–13]

One possible organizing contribution is not a new estimator, controller, contract formalism, or recovery mechanism in isolation, but the treatment of **controlled-object lifting itself** as the object of study: which favorable properties of protocol-constituted state survive when the controlled object becomes inferred, mediated, autonomous, composed, and dynamically reconfigured?

That statement is a research hypothesis, not a novelty conclusion. Search particularly for prior work using simulation or refinement relations between replicated state and physical state, Byzantine partially observable games, adversarial contract composition, distributed runtime enforcement, resilient active diagnosis, and fault-containment models with correlated compromise.

---

## 12. Immediate research agenda

One disciplined first program is:

1. **Give two or three precise control reconstructions of standard BFT.** Compare state-invariance, trace-control, and epistemic formulations on the same protocol.
2. **Define liftability using a relation between base and generalized executions.** Avoid assuming that a projection or exact state estimate always exists.
3. **Prove one information-theoretic non-lift result.** The indistinguishability template is the natural candidate.
4. **Prove one estimator–controller composition result.** Begin with finite state and explicit ambiguity sets.
5. **Show one case where agreement on an action certificate suffices without agreement on a point state.** This tests the minimal-coordination question.
6. **Develop one compositional counterexample with a shared fault cause.** Use it to refine the contract language.
7. **Only then add capability-changing or coercive actions.** Derive their necessity from an unmediated-transition obstruction rather than assuming them at the outset.

At each stage, preserve the distinction between:

\[
\text{what is true},\quad
\text{what is observed},\quad
\text{what is certified},\quad
\text{what is agreed},\quad
\text{what is authorized},\quad
\text{what actually changes}.
\]

The generalization succeeds only when the relations among those objects are strong enough for the target property. Determining those relations—not naming a finished architecture—is the research problem.

---

## References

[1] Leslie Lamport, Robert Shostak, and Marshall Pease. “The Byzantine Generals Problem.” *ACM Transactions on Programming Languages and Systems* 4(3), 1982, 382–401. DOI: 10.1145/357172.357176.

[2] Miguel Castro and Barbara Liskov. “Practical Byzantine Fault Tolerance.” *Proceedings of OSDI*, 1999, 173–186.

[3] Danny Dolev, Nancy A. Lynch, Shlomit S. Pinter, Eugene W. Stark, and William E. Weihl. “Reaching Approximate Agreement in the Presence of Faults.” *Journal of the ACM* 33(3), 1986, 499–516.

[4] Aritra Mitra and Shreyas Sundaram. “Byzantine-Resilient Distributed Observers for LTI Systems.” *Automatica* 108, 2019, 108487. DOI: 10.1016/j.automatica.2019.06.039.

[5] Yuxiao Chen, James Anderson, Karanjit Kalsi, Aaron D. Ames, and Steven H. Low. “Safety-Critical Control Synthesis for Network Systems with Control Barrier Functions and Assume-Guarantee Contracts.” *IEEE Transactions on Control of Network Systems* 8(1), 2021, 487–499. DOI: 10.1109/TCNS.2020.3029183.

[6] Xuan Wang, Shaoshuai Mou, and Shreyas Sundaram. “Resilience for Distributed Consensus with Constraints.” *IEEE Transactions on Automatic Control* 70(10), 2025, 6704–6718. DOI: 10.1109/TAC.2025.3565681.

[7] Yu Wang, Alper Kamil Bozkurt, Nathan Smith, and Miroslav Pajic. “Attack-Resilient Supervisory Control of Discrete-Event Systems: A Finite-State Transducer Approach.” *IEEE Open Journal of Control Systems*, 2023. DOI: 10.1109/OJCSYS.2023.3290408.

[8] Roderick Bloem, Bettina Könighofer, Robert Könighofer, and Chao Wang. “Shield Synthesis: Runtime Enforcement for Reactive Systems.” *TACAS*, 2015, 533–548. DOI: 10.1007/978-3-662-46681-0_51.

[9] D. Seto, B. H. Krogh, L. Sha, and A. Chutinan. “The Simplex Architecture for Safe Online Control System Upgrades.” *Proceedings of the 1998 American Control Conference*, vol. 6, 3504–3508. DOI: 10.1109/ACC.1998.703255.

[10] Aaron D. Ames, Xiangru Xu, Jessy W. Grizzle, and Paulo Tabuada. “Control Barrier Function Based Quadratic Programs for Safety Critical Systems.” *IEEE Transactions on Automatic Control* 62(8), 2017, 3861–3876. DOI: 10.1109/TAC.2016.2638961.

[11] Andreas Haeberlen, Petr Kouznetsov, and Peter Druschel. “The Case for Byzantine Fault Detection.” *HotDep*, 2006.

[12] Miguel Castro and Barbara Liskov. “Proactive Recovery in a Byzantine-Fault-Tolerant System.” *OSDI*, 2000.

[13] Jaynarayan H. Lala and Richard E. Harper. “Architectural Principles for Safety-Critical Real-Time Applications.” *Proceedings of the IEEE* 82(1), 1994, 25–40. DOI: 10.1109/5.259424.
