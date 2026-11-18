# Byzantine Invariant Control: A Research Note and LLM Handoff Specification

## 0. Working thesis

Byzantine Fault Tolerance can be read as a theory of **distributed epistemic control**: a set of replicas maintains agreement about an abstract state despite arbitrary, malicious, or faulty behavior by some participants. The proposed generalization is to ask for a theory of **distributed invariant control**: a set of controllers embedded in the system they control must maintain specified invariants over informational, economic, organizational, cyber-physical, legal, and physical state, despite Byzantine behavior by some controllers, sensors, actuators, or governed nodes.

The key shift is this:

> Consensus is not control. Consensus is an informational precondition for control.

Classical BFT gives protocols by which honest participants can agree in the presence of arbitrary faulty behavior; Lamport, Shostak, and Pease framed the canonical Byzantine agreement problem, and Castro and Liskov later made Byzantine replication practical for asynchronous networked systems. But an external-world invariant—no unsafe vehicle separation, no invalid asset transfer, no unlicensed reactor operation, no uncontrolled release of hazardous material, no unauthorized model deployment—requires more than agreement. It requires sensors, authority, actuation, enforcement, and recovery.

A good name for the narrow research object is **Byzantine Invariant Control**. A more general name is **Adversarial Distributed Invariant Control**. The former preserves continuity with BFT; the latter correctly centers the invariant, not the fault model.

## 1. The object being generalized

Let a distributed system have global state (X_t), local node states (x_{i,t}), controllers (C_i), sensors (S_i), actuators (A_i), and communication relation (G_t). Let (K \subseteq \mathcal{X}) be an admissible region of system state. An invariant is a predicate or state constraint:

[
I(X_t) = \texttt{true}
]

or equivalently:

[
X_t \in K.
]

The research problem is to design a distributed closed-loop system such that, for all admissible disturbances and up to a specified adversarial budget, the system remains inside (K), or returns to a recoverable subset of (K), while maintaining accountable control over the controllers themselves.

This makes BFT a special case. In consensus, the invariant is usually an agreement property, such as:

[
\forall i,j \in H,\quad d_i = d_j
]

where (H) is the set of honest nodes and (d_i) is node (i)’s decision value. In invariant control, agreement is only one possible invariant. The invariant may concern physical separation, supply conservation, credential validity, reserve backing, safety envelopes, emissions limits, jurisdictional compliance, or the membership of the controller set itself.

The technical gap is that BFT normally terminates at **state-machine replication** or agreement over commands, whereas invariant control must continue into **world-coupled actuation**. Existing adjacent literatures cover parts of this: secure estimation/control studies corrupted sensors and actuators in cyber-physical systems; resilient multi-agent control studies consensus and optimization under malicious agents; control barrier functions and viability theory formalize safety as controlled set invariance; STPA models unsafe control actions and feedback failures; runtime verification/enforcement monitors temporal properties in distributed systems. The proposed research problem is their integration under Byzantine membership, endogenous authority, and coercive actuation.

## 2. Why informational consensus is insufficient

Informational BFT answers questions of the form:

> What should the honest replicas believe, decide, or append?

Invariant control asks a harder question:

> What must the system be able to do, after deciding, so that the invariant remains true?

For ledger-only systems, the world is mostly endogenous to the replicated state machine. If validators agree that a transaction is invalid, the invalid transaction does not enter the ledger. But for cyber-physical, organizational, or legal systems, invalidity in the ledger does not prevent invalidity in the world. A validator can be expelled from a committee, but a corrupt plant operator may still open a valve. A key can be revoked, but a former controller may still possess physical access. A DAO can vote to freeze an account, but it cannot automatically seize an off-chain warehouse. A traffic-control system can agree that a vehicle is unsafe, but the vehicle still needs braking authority, road authority, or police authority.

Thus the generalized theory requires an explicit distinction between:

1. **epistemic authority**: who can know, attest, classify, or certify system state;
2. **decisional authority**: who can transform observations into authorized commands;
3. **actuator authority**: who can change the world;
4. **membership authority**: who can add, remove, quarantine, or demote controllers;
5. **coercive authority**: who can impose sanctions despite non-cooperation;
6. **constitutional authority**: who can change the rules by which all other authorities operate.

The word “police” is suggestive but too institution-specific. The more canonical primitive is a **coercive actuator set**: a set of mechanisms that can force, disable, seize, isolate, revoke, or physically interdict a node or asset. The police force is one implementation. Others include slashing, key revocation, access denial, routing exclusion, license suspension, facility lockout, injunction, physical seizure, failover, or remote shutdown.

(Perhaps because BFT emerged from distributed computing rather than control theory, it treats agreement as the main achievement. In world-coupled systems, agreement is only the point at which the control problem becomes explicit.)

## 3. Proposed definition

**Byzantine Invariant Control** is the study of distributed architectures that preserve specified system invariants under arbitrary faulty, malicious, strategically deceptive, or non-compliant behavior by a bounded subset of participants, including participants who may be controllers, sensors, actuators, enforcers, or rule-makers.

The system is **endogenous** when the controllers exist inside the state space whose invariants they are meant to preserve. This is the important case. If the enforcing authority sits outside the model, the theory has hidden a centralized trusted party. A serious theory must treat the police layer, validator layer, sensor layer, and governance layer as potentially Byzantine.

A minimal formal schema:

```text
structure BIC_Instance:
  X          : state space
  K          : admissible invariant region, K ⊆ X
  N          : nodes/controllers
  H, B       : honest/Byzantine partition, unknown to controllers
  Obs_i      : local observation function for node i
  Msg        : communication protocol
  Dec        : distributed decision/authorization rule
  Act        : actuator family, including coercive actuators
  Auth       : authority relation over actions
  Cost       : cost/risk function over interventions
  Rec        : recovery relation after violation or near-violation

BIC objective:
  synthesize distributed policies π_i such that
    for all Byzantine behaviors b ∈ B,
    for all admissible disturbances w,
    the closed-loop trajectory either remains in K
    or enters a recoverable subset R ⊆ K before loss,
  while every coercive action remains authorized, auditable, and contestable.
```

This schema deliberately separates (K), the invariant region, from (R), the recoverable region. Some real systems cannot guarantee strict invariance at every instant. They can only guarantee bounded violation, fast containment, or reversible excursion. That distinction matters. A ledger validity invariant may be hard safety: invalid states are never admitted. A physical safety invariant may require a viability kernel: states from which some admissible control policy can keep the system inside constraints. Viability theory explicitly studies controlled evolution under state constraints and viability kernels; barrier certificates and control barrier functions likewise formalize safety through invariant or forward-invariant sets.

## 4. Action primitives required for feasibility

The required action set should be described by its control function rather than by institutional metaphor. The core primitives are:

| Control function        | Scale-specified examples                                                        | Purpose                                                     | Failure mode if absent                                               |
| ----------------------- | ------------------------------------------------------------------------------- | ----------------------------------------------------------- | -------------------------------------------------------------------- |
| Observation             | sensor reading, attestation, audit log, inspection, witness report              | Determine whether the invariant is endangered               | The system cannot distinguish adversary, noise, and normal variation |
| Authentication          | signature, credential, license, badge, hardware identity                        | Bind actions to accountable agents                          | Byzantine nodes can spoof authority                                  |
| Agreement               | BFT vote, quorum certificate, threshold signature, replicated log               | Produce common knowledge or authorized decision             | Honest controllers fragment into inconsistent actions                |
| Quarantine              | isolate process, disconnect node, disable route, suspend account, lock facility | Prevent suspected damage propagation before final judgment  | The system waits for certainty and loses the invariant               |
| Exclusion               | expel validator, revoke operator role, delist sensor, remove controller         | Remove a corrupted participant from the control surface     | Byzantine participation persists indefinitely                        |
| Substitution            | failover, backup controller, reserve operator, redundant actuator               | Preserve function after removal                             | Exclusion destroys service continuity                                |
| Preemption              | command override, emergency stop, denied transaction, safety shield             | Block unsafe local actions before they become global losses | Local autonomy can violate global invariants                         |
| Sanction                | slashing, bond call, clawback, legal penalty, license revocation                | Change incentives and impose cost on violation              | Rational adversaries face no deterrent                               |
| Coercion                | seizure, arrest, physical interdiction, access denial, equipment disablement    | Enforce decisions against non-consenting agents             | External-world invariants remain voluntary                           |
| Appeal                  | challenge window, evidence review, reversal, compensation                       | Constrain false positives and abusive enforcement           | The police layer becomes the Byzantine adversary                     |
| Constitutional revision | rule update, emergency governance, actuator re-scoping                          | Adapt to model failure or new attack classes                | The system preserves obsolete invariants or unsafe rules             |

This table is not a random checklist. It is ordered by the transition from **information** to **authorization** to **actuation** to **legitimacy repair**. Feasible invariant control requires the whole chain. Weak systems tend to have either epistemic capacity without actuation, or coercive actuation without trustworthy epistemics.

The most dangerous design error is to add coercion without Byzantine-hardening the coercive layer. A police force, court, multisig council, foundation, safety board, model-ops team, or emergency committee is itself a controller. It must be modeled as corruptible, captureable, mistaken, delayed, misinformed, or overreaching.

## 5. The action lattice: coerciveness, reversibility, and coupling

A control action should be typed along at least six dimensions:

| Dimension          | Low value              | High value                                 | Why it matters                                                   |
| ------------------ | ---------------------- | ------------------------------------------ | ---------------------------------------------------------------- |
| World-coupling     | ledger entry           | physical interdiction                      | Determines whether consensus suffices                            |
| Coerciveness       | recommendation         | forced removal                             | Determines legitimacy burden                                     |
| Reversibility      | reversible label       | irreversible destruction or arrest         | Determines appeal and evidentiary standard                       |
| Latency tolerance  | days                   | milliseconds                               | Determines whether deliberation is possible                      |
| Locality           | single node            | jurisdiction-scale infrastructure          | Determines governance scale                                      |
| Byzantine exposure | action by one operator | threshold-controlled distributed actuation | Determines whether the action channel becomes the attack surface |

This gives a design rule:

> The stronger, less reversible, more world-coupled, and lower-latency the action, the stronger the authorization, audit, and appeal structure must be.

This rule prevents the “just add a police force” move from becoming theoretically sloppy. The theory does require coercive actuators, but coercion is not a scalar. Freezing an API key, rotating a validator set, impounding a truck, arresting an operator, and shutting down a substation are different action types with different reversibility, latency, and evidentiary burdens.

## 6. Feasibility conditions

A Byzantine invariant-control system is feasible only if the following conditions can be satisfied.

### 6.1 Observability condition

The system must observe enough state to detect imminent invariant violation before the viability boundary is crossed. If (K) is the admissible region, then the system needs warning inside a margin (M \subseteq K), not only after (X_t \notin K). Runtime verification studies how systems can monitor executions against formal properties, including in distributed contexts where there may be no single global observation point.

### 6.2 Attribution condition

The system must distinguish sensor fault, actuator fault, controller fault, communication fault, and adversarial manipulation well enough to choose an intervention. Perfect attribution is not always necessary, but the action class must match attribution confidence. Quarantine may require suspicion; irreversible sanction should require stronger evidence.

### 6.3 Authorization condition

The system must have a procedure for converting observations into legitimate commands. For digital actions this may be quorum certification or threshold signing. For external-world actions it may require legal process, organizational mandate, or pre-authorized emergency procedure.

### 6.4 Actuation condition

There must exist at least one action sequence capable of keeping the state inside (K) or returning it to a recoverable subset. If no actuator can affect the relevant state variable, the invariant is aspirational rather than controlled.

### 6.5 Redundancy condition

Removal of a corrupt node must not remove the system’s ability to preserve the invariant. This implies spare capacity, alternate communication paths, backup controllers, redundant sensors, or fallback procedures.

### 6.6 Containment condition

A suspected Byzantine component must be containable faster than it can propagate unrecoverable damage. This is the quarantine principle.

### 6.7 Accountability condition

The enforcement layer must leave evidence. Coercive invariant control without forensic trace becomes indistinguishable from arbitrary domination.

### 6.8 Contestability condition

Since the coercive layer can itself be Byzantine, mistaken, or captured, the system needs appeal, rollback, compensation, or counter-control. This is not a liberal ornament; it is a Byzantine-resilience requirement for the enforcement layer.

### 6.9 Constitutional condition

The system needs rules for changing invariant definitions, membership rules, and actuator scopes. Otherwise the invariant-control system cannot adapt when the environment changes or when the original specification is discovered to be unsafe.

## 7. The central research questions

The research agenda can be posed as seven linked synthesis problems.

### Problem 1: Invariant specification

How should invariants be represented across hybrid informational, economic, legal, organizational, and physical state? Candidate languages include temporal logic, state predicates, control barrier functions, assume-guarantee contracts, legal rules, and operational safety constraints. The hard case is not a pure mathematical invariant; it is a mixed invariant whose satisfaction depends on records, incentives, permissions, physical positions, and institutional recognition.

### Problem 2: Byzantine observability

What observations are sufficient when sensors, witnesses, auditors, logs, and validators may be Byzantine? This generalizes secure state estimation, where the system estimates state despite corrupted sensors or actuators.

### Problem 3: Distributed authorization

What threshold, quorum, or constitutional mechanisms should authorize each action class? The authorization threshold should depend on reversibility, urgency, evidence quality, and coerciveness.

### Problem 4: Actuator synthesis

Given invariant (K), adversary budget (f), topology (G), actuator set (A), and latency bound (\Delta), determine whether there exists a distributed policy that preserves (K). If yes, synthesize it. If no, identify the missing actuator, sensor, redundancy, or authority.

### Problem 5: Coercive membership control

How can the system remove or quarantine Byzantine nodes without granting unchecked power to the removers? This is the “police problem.” The police layer must be strong enough to remove malicious actors and constrained enough not to become the malicious actor.

### Problem 6: Recovery and compensation

When strict invariance is impossible, what recovery guarantees are acceptable? How should the system compensate for false positives, failed interventions, or coercive mistakes?

### Problem 7: Self-reference and constitutional recursion

How does the system control invariants over its own controllers? This includes membership, authority, monitoring, enforcement, appeal, and rule revision. A theory that assumes an incorruptible meta-controller is not a Byzantine theory.

## 8. Relationship to STPA

STPA is especially relevant because it treats safety as a control problem rather than merely as component reliability. It asks analysts to model controllers, controlled processes, control actions, and feedback, then identify unsafe control actions and causal scenarios. Byzantine Invariant Control can be read as an adversarial, distributed, formally synthesizable extension of this attitude.

The STPA-style question is:

> What unsafe control actions can drive the system out of its invariant region?

The Byzantine-control extension is:

> What if the unsafe control action is intentionally generated, strategically hidden, quorum-certified by compromised participants, or enforced by a captured police layer?

That is the research seam.

## 9. Benchmark domains

A useful research program needs benchmark domains with increasing world-coupling.

| Domain                       | Invariant                                                       | Byzantine actors                                    | Required actuators                                          |
| ---------------------------- | --------------------------------------------------------------- | --------------------------------------------------- | ----------------------------------------------------------- |
| Replicated ledger            | Honest nodes do not finalize conflicting histories              | validators, clients, relays                         | reject block, slash, rotate validator set                   |
| Stablecoin or reserve system | Issued claims do not exceed admissible collateral               | oracles, custodians, governance, issuers            | freeze minting, audit, seize collateral, revoke issuer      |
| AI deployment network        | No model above risk class (r) is deployed without authorization | labs, evaluators, cloud providers, auditors         | deny compute, revoke API, block release, inspect facility   |
| Autonomous traffic           | Vehicles maintain safe separation                               | vehicles, sensors, roadside units, fleet operators  | brake, reroute, revoke autonomy, physical stop              |
| Power grid                   | Frequency and load remain inside safe envelope                  | sensors, generators, operators, market participants | dispatch, islanding, disconnect, blackstart                 |
| Biosecurity supply chain     | Controlled materials remain within licensed chain of custody    | labs, shippers, inspectors, registries              | deny transfer, seize material, revoke license, inspect site |

These domains are ordered by increasing world-coupling and decreasing sufficiency of informational consensus. A ledger can often enforce its own state transition rules internally. A biosecurity supply chain cannot.

## 10. Minimal output of the theory

A mature theory should produce at least four artifacts.

First, it should produce **diagnostic maps**: for a proposed system, identify which invariants are merely asserted, which are monitored, which are enforceable, and which are enforceable only by trusted external authority.

Second, it should produce **feasibility theorems**: given adversary budget, topology, observability, actuator authority, and latency, determine whether invariant preservation is possible.

Third, it should produce **synthesis methods**: construct controllers, monitors, quorum rules, sanctions, fallback policies, and appeal structures.

Fourth, it should produce **constitutional design principles**: prevent the enforcement layer from becoming the unmodeled source of Byzantine failure.

## 11. Suggested terminology

Use **Byzantine Invariant Control** when the adversary model is specifically Byzantine: arbitrary behavior by a bounded subset of participants.

Use **Adversarial Distributed Invariant Control** when the adversary model includes Byzantine, rational, stochastic, negligent, captured, or institutionally misaligned behavior.

Use **coercive actuator** instead of “police” when discussing the abstract theory.

Use **world-coupled invariant** for an invariant whose truth is not determined solely by the replicated informational state.

Use **endogenous controller** for a controller that is itself part of the system state and therefore subject to the same invariants, incentives, faults, and enforcement mechanisms as other nodes.

Use **constitutional control** for control over the rules that define membership, authority, invariants, and enforcement.

## 12. LLM handoff instructions

When given a system to analyze under this research program, do not start by asking whether the system has consensus. Start by identifying the invariant and the actuator chain.

For any proposed system, produce the following analysis:

1. State the system boundary at a specific scale: node, subnet, organization, facility, jurisdiction, market, or physical infrastructure.
2. Define the invariant (K). Say whether it is informational, economic, cyber-physical, legal, physical, or mixed.
3. Identify the controlled state variables (X) and the local observations available to each controller.
4. Identify all controllers, sensors, actuators, governed nodes, auditors, and enforcement bodies.
5. Specify the Byzantine model: which roles may be corrupt, how many, with what capabilities, and at what latency.
6. Separate epistemic consensus from actuation. Say what agreement can establish, and what it cannot enforce.
7. List available action primitives: observe, attest, certify, quarantine, exclude, substitute, revoke, preempt, sanction, coerce, appeal, revise.
8. Classify each action by world-coupling, coerciveness, reversibility, latency tolerance, locality, and Byzantine exposure.
9. Determine whether the invariant is strictly enforceable, recoverably enforceable, only monitorable, or merely aspirational.
10. Identify the weakest missing element: observability, attribution, authorization, actuation, redundancy, containment, accountability, contestability, or constitutional revision.
11. Propose a revised architecture that closes the gap without assuming an incorruptible meta-controller.
12. Explicitly analyze how the enforcement layer can fail or be captured.
13. Produce at least one attack scenario in which the police/coercive actuator layer is Byzantine.
14. Produce at least one false-positive scenario in which honest nodes are wrongly removed.
15. Recommend safeguards proportional to the coerciveness and irreversibility of each action.

The central instruction is:

> Treat every controller, including the enforcer, as inside the model.

If an answer relies on “the authorities intervene,” “the foundation removes them,” “the multisig freezes it,” “the police enforce it,” or “the operator shuts it down,” then expand that phrase into sensors, decision rules, authorization thresholds, actuator channels, latency bounds, audit trails, and appeal mechanisms. Otherwise the answer has smuggled in a trusted third party.

## 13. Research agenda in one paragraph

Byzantine Invariant Control asks how distributed systems whose controllers are themselves embedded in the system can preserve specified invariants under arbitrary adversarial behavior. It generalizes BFT from agreement over replicated informational state to closed-loop control over world-coupled state. The central problem is not merely how honest nodes agree, but how agreement becomes authorized, accountable, and coercive action without creating an unmodeled sovereign adversary. The field should integrate Byzantine consensus, resilient distributed control, secure cyber-physical estimation, viability theory, control barrier functions, runtime enforcement, STPA, mechanism design, and institutional theory into a synthesis discipline for invariant-preserving distributed systems.
