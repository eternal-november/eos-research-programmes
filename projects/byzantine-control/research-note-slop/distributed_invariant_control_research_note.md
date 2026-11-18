# Distributed Invariant Control under Byzantine Conditions
## A research problem, analytic instrument, and machine-operational agenda

**Working abbreviation:** B-DIC (Byzantine Distributed Invariant Control)
**Status:** research-framing note
**Scope:** distributed systems whose controllers, sensors, actuators, members, and enforcement institutions are themselves contained in the controlled system.

## Abstract

Byzantine fault tolerance (BFT) is principally a theory of maintaining informational properties—agreement, non-equivocation, valid replicated state transitions, and conditional progress—despite arbitrary behavior by a bounded subset of participants. A world-coupled distributed system requires a stronger object. Its controllers must preserve invariants over a joint cyber-physical-institutional state: not only what the ledger says, but which valves are open, which machines may issue commands, which persons or organizations possess authority, which resources remain under custody, and whether the enforcement apparatus itself remains within its mandate.

The proposed research problem is therefore:

> **Synthesize distributed, Byzantine-resilient policies and actuator architectures that keep an endogenous system inside a specified invariant set, while preserving a specified service floor and constraining the interventions used to do so.**

The crucial addition to BFT is not merely “more consensus” and not necessarily a police force. It is an **enforcement substrate**: a capability-specified collection of actions that can block, preempt, attenuate, revoke, quarantine, substitute, sequester, disconnect, or physically restrain invariant-relevant agency. A police force is one possible terminal actuator where humans or organizations retain extra-protocol physical capabilities. In systems designed with complete mediation, fail-safe interlocks, revocable authority leases, and takeover capacity, less dramatic actions may suffice.

This note supplies a formal model, an intervention algebra, a seven-closure feasibility criterion, candidate impossibility and synthesis results, a reference architecture, a research program, a domain-analysis instrument, and a self-contained prompt suitable for delegation to another LLM.

---

## 1. Research thesis

The generalization from BFT to distributed invariant control is not:

> “Run BFT consensus, then execute whatever the ledger decides.”

It is:

> “Treat sensing, agreement, authorization, actuation, containment, replacement, and enforcement as one adversarially specified closed-loop system, and prove that the resulting joint system preserves its invariants.”

This distinction matters because agreement is neither truth nor compliance. Correct replicas may agree on false sensor reports. They may agree on a command that is already too late. A valid command may be rejected by a compromised actuator. A node removed from consensus membership may continue operating a pump, vehicle, bank account, factory, armed unit, or administrative office. Conversely, removing a controller may itself destroy safety if no replacement can assume its function.

The generic field name should therefore be **Distributed Invariant Control (DIC)**. The Byzantine threat-qualified subproblem is **Distributed Invariant Control under Byzantine Conditions**, abbreviated **B-DIC**. “Byzantine control” is usable as informal shorthand, but it hides the controlled object and can be misread as control *by* Byzantine agents rather than control *despite* them.

A further qualifier is useful:

> **Reflexive B-DIC** denotes the case in which the controllers, enforcers, membership rules, authority allocations, and repair mechanisms are all components of the state over which the invariant is defined.

Reflexivity prevents the theory from quietly placing a perfectly trusted police, court, administrator, safety controller, or hardware root outside the model.

---

## 2. What is being generalized

Classical BFT and B-DIC can be related as follows.

| Structural dimension | Informational BFT | B-DIC |
|---|---|---|
| Controlled object | Replicated log, state machine, or decision value | Joint physical, cyber, organizational, authority, and evidence state |
| Primary safety property | Honest replicas do not decide or commit conflicting states | Every admissible execution remains inside a specified invariant set |
| Primary liveness property | Requests eventually execute under network and fault assumptions | A specified service floor, recovery objective, or mission property remains achievable |
| Adversarial behavior | Arbitrary protocol behavior by a bounded node set | Arbitrary behavior within each corrupted actor’s physically and institutionally available capability set |
| Principal output | Ordered value, block, state transition, or certificate | A certified intervention coupled to an effective actuator path |
| Membership action | Add, remove, or reconfigure protocol participants | Alter informational membership **and** invariant-relevant capabilities, custody, roles, and physical access |
| Time model | Usually round-, synchrony-, or finality-specified | Also plant-dynamics-, reaction-horizon-, and irreversibility-specified |
| Failure of guarantee | Fork, inconsistent decision, or loss of progress | Physical harm, unauthorized transfer, loss of containment, rights violation, or collapse of service capacity |

BFT state-machine replication already combines agreement with execution of a deterministic service, but its correctness boundary normally ends at the replicated service interface. Practical BFT work establishes that replicas can agree and execute despite arbitrary replica faults; it does not by itself establish that external sensors report truth or that external effectors obey. Adjacent control work instead treats safety as forward invariance, runtime assurance, or resilient coordination, often under materially narrower assumptions about sensing, actuation, agent compliance, or system membership. The B-DIC problem is to unify those interfaces rather than treat them as separate trusted seams. [R1–R9]

---

## 3. Formal problem statement

### 3.1 Endogenous state

Let the joint state space be

\[
X = X_P \times X_C \times X_I \times X_E,
\]

where:

- \(X_P\) is plant or world state: positions, inventories, balances, pressures, network flows, custody, possession, and other materially relevant variables;
- \(X_C\) is controller and computation state: local memories, software modes, keys, model parameters, clocks, and protocol state;
- \(X_I\) is institutional state: membership, roles, credentials, authority leases, liabilities, jurisdictions, delegation relations, and resource ownership or custody;
- \(X_E\) is evidentiary state: attestations, audit logs, fault proofs, confidence bounds, provenance, and unresolved disputes.

The inclusion of \(X_I\) and \(X_E\) is essential. Expulsion, key revocation, asset freezing, physical lockout, and reinstatement are not exogenous administrative events; they are state transitions generated by controllers inside the system.

### 3.2 Invariants

A state invariant is a predicate

\[
K : X \to \mathsf{Prop},
\]

or extensionally a safe set \(\mathcal K = \{x\in X \mid K(x)\}\).

A realistic specification usually has several conjuncts:

\[
K(x) \equiv K_{plant}(x) \land K_{authority}(x) \land K_{service}(x) \land K_{meta}(x).
\]

Examples include:

- a physical envelope, such as pressure below a specified limit;
- a conservation invariant, such as no asset created without an authorized issuance transition;
- an authority invariant, such as no actuator accepting a command lacking a valid threshold certificate;
- a service-floor invariant, such as at least one independent safe controller remaining operational;
- a constitutional or meta-invariant, such as no coercive intervention exceeding its certified scope or duration.

Temporal safety properties can be converted into state invariants by taking the product of \(X\) with a monitor automaton. Liveness should remain separately specified because indefinite shutdown can preserve many safety invariants while destroying the purpose of the system.

### 3.3 Capability-specified Byzantine behavior

Let \(N\) be the node or actor type and \(A\) the primitive action type. Each actor has a state-dependent capability set

\[
\mathsf{Cap}_x(i) \subseteq A.
\]

A Byzantine actor may choose arbitrary actions, send inconsistent messages, withhold cooperation, corrupt its local state, or collude, but only within \(\mathsf{Cap}_x(i)\) and the physical transition relation. “Byzantine” is protocol-arbitrary, not physics-arbitrary.

This capability specification is the bridge between fault tolerance and coercive control. An enforcement action can change \(\mathsf{Cap}_x(i)\): revoking a key, disabling an API, opening a breaker, transferring custody, restricting movement, or physically removing an operator all alter what future transitions the target can cause.

Fault budgets should be domain-specified rather than collapsed into one scalar. A model may contain

\[
(f_C,f_S,f_A,f_E),
\]

for corrupted controllers, sensors, actuators, and enforcers respectively. Correlation assumptions must also be explicit: two nominally independent nodes operated by one organization may constitute one failure domain.

### 3.4 Dynamics and information

For a discrete-time presentation, let

\[
x_{t+1} \in F(x_t, u^H_t, u^B_t, w_t),
\]

where \(u^H_t\) is the joint action of correct controllers and enforcers, \(u^B_t\) is the joint action of Byzantine actors, and \(w_t\) is an admissible environmental disturbance.

Each correct controller \(i\) has a local history \(h^i_t\), formed from its observations, received messages, certificates, and prior local actions. Its policy is

\[
\pi_i : H_i \to A_i.
\]

Byzantine strategies are arbitrary history-dependent maps subject to their capability envelopes and the selected fault model. Communication schedules, sensor errors, actuator delays, and model uncertainty belong in the execution quantifiers, not in prose outside the theorem.

A compact type-theoretic schema is:

```text
structure BDICInstance where
  X            : Type                 -- endogenous joint state
  Node         : Type
  Observation  : Type
  Action       : Type
  Disturbance  : Type
  Safe         : X -> Prop
  Cap          : X -> Node -> Set Action
  Observe      : Node -> X -> Set Observation
  Next         : X -> (Node -> Action) -> Disturbance -> Set X
  FaultAdmissible : Set Node -> Prop
```

A complete formalization would add time, authentication, communication schedules, authority certificates, stochastic kernels where needed, and a semantics for organizations controlling multiple nodes.

### 3.5 Solution concept

Let \(\mathcal R\subseteq\mathcal K\) be a **robust recoverable set**. A B-DIC architecture solves the safety problem on \(\mathcal R\) when

\[
\forall x_0\in\mathcal R,\;\forall \beta\in\mathcal B,\;\forall w\in\mathcal W,\;\forall \sigma\in\Sigma:
\quad x_t\in\mathcal K\;\text{for every }t,
\]

where \(\beta\) ranges over admissible Byzantine strategies and \(\sigma\) over admissible network and execution schedules.

It solves the full control problem when it also satisfies a liveness or mission specification \(L\) under explicitly stronger environmental and synchrony assumptions.

The recoverable set is generally smaller than the nominal safe set. A state may be safe at the present instant but already too close to the boundary for a delayed distributed intervention to prevent escape.

---

## 4. The consensus-to-control separation

BFT can remain the informational coordination substrate, but five additional interfaces determine whether it becomes control.

| Interface | What agreement can establish | What remains unestablished |
|---|---|---|
| Epistemic | Honest replicas agree on received reports or a computed estimate | Reports correspond to the world; hidden state is bounded tightly enough for safe action |
| Semantic/model | Honest replicas execute the same transition function | The model predicts the world accurately over the intervention horizon |
| Decisional | Correct replicas do not issue conflicting certified commands | A safe command exists and is selected before recoverability is lost |
| Authority | A quorum has certified a command | The certificate binds the relevant actuator, custodian, institution, or human organization |
| Actuation | The command is durably recorded | The effect occurs, occurs once, occurs within scope, and cannot be bypassed or reversed by a Byzantine actor |

The ledger is therefore best modeled as an **evidence-and-command coordination service**, not as the complete controller. Its output becomes control only through an authority relation and an actuator relation.

This yields a basic separation principle:

> **Agreement is a property of distributed beliefs or commitments. Invariance is a property of reachable world trajectories. A theorem connecting them requires explicit observation, authority, actuation, and timing assumptions.**

---

## 5. An intervention algebra

### 5.1 Coercion as capability change

Let an intervention \(e\) induce a state transformer \(\rho_e:X\to X\). It is **capability-restricting** for target \(j\) at state \(x\) when

\[
\mathsf{Cap}_{\rho_e(x)}(j) \subsetneq \mathsf{Cap}_x(j).
\]

It is **coercive** when the restriction does not depend on contemporaneous authorization from \(j\). This definition is broader and cleaner than equating coercion with violence. Rate limits, credential revocation, escrow seizure, network quarantine, mechanical lockout, and arrest all restrict effective action sets at different world-coupling levels.

A node is **logically expelled** when it loses protocol membership. It is **effectively excluded** from invariant-relevant control only when it also loses every action channel whose use can force a violation, except channels already bounded in the disturbance model.

### 5.2 Primitive intervention families

The following ontology is organized by the state component each action primarily changes.

| Intervention family | Primitive actions | Primary state effect | Typical purpose |
|---|---|---|---|
| Evidence | sample, attest, challenge, inspect, audit, preserve, cross-check | Narrows or records the controller belief state | Detect equivocation, model uncertainty, hidden damage, or false reports |
| Decision | propose, vote, certify, veto, order, checkpoint | Creates a common authorized commitment | Prevent conflicting interventions and establish a verifiable command |
| Capability | grant, lease, attenuate, rate-limit, revoke, quarantine, geofence | Changes a target’s feasible digital or institutional action set | Contain future influence before physical harm occurs |
| Operational | filter, suppress, preempt, override, switch, isolate, shut down | Changes current command flow or plant input | Block an imminent unsafe transition |
| Continuity | replicate, fail over, substitute, reassign, reconfigure, degrade | Changes role occupancy and service capacity | Preserve control after containment or removal |
| Custodial/resource | freeze, escrow, seize, disconnect, immobilize, impound, deny access | Changes possession, custody, energy, money, or physical affordances | Enforce decisions against noncooperation |
| Repair/reintegration | rollback, recover, patch, rotate, rehabilitate, reinstate | Restores recoverability and possibly capability | Avoid permanent degradation and accumulated exclusions |
| Constitutional | scope, time-limit, log, review, appeal, ratify, reverse | Constrains the enforcement substrate itself | Prevent the enforcer from becoming the dominant Byzantine actor |

A conceptual inductive type is:

```text
inductive Intervention
| attest      (observer target claim evidence)
| certify     (policy command quorum_proof)
| fence       (target capability_scope expiry)
| preempt     (actuator safe_command)
| substitute  (role incumbent replacement)
| sequester   (resource new_custodian)
| isolate     (region boundary_conditions)
| repair      (target recovery_plan)
| reinstate   (target capability_scope)
| review      (intervention adjudication_rule)
```

“Remove node” should not be treated as one primitive. Effective removal normally expands to:

\[
\text{evidence} \to \text{fault certificate} \to \text{authority revocation} \to
\text{channel isolation} \to \text{actuator preemption} \to
\text{role substitution} \to \text{repair or custodial action}.
\]

A police force implements some custodial and physical actions. It does not supply the preceding epistemic, decisional, timing, or continuity guarantees.

---

## 6. The seven-closure feasibility criterion

The following conditions are proposed as an analytic criterion. They are not yet claimed to be jointly necessary and sufficient in every model; part of the research program is to identify exact theorem classes.

### 6.1 Boundary closure

Every transition capable of violating \(K\) must be represented as one of:

1. a controllable action mediated by the architecture;
2. a Byzantine action bounded by a specified capability envelope;
3. an environmental disturbance bounded by \(\mathcal W\).

An unmodeled manual bypass, off-ledger asset transfer, alternate communication channel, independent weapon, hidden administrator credential, or external organization with relevant force breaks boundary closure.

Boundary closure does not require that everything be controllable. It requires that uncontrollable influence be bounded strongly enough for a robust invariant to exist.

### 6.2 Epistemic closure

Correct controllers must maintain a sound set-valued belief \(B_t\subseteq X\) containing the true state. Safety requires an action that works for every state and adversarial continuation still considered possible:

\[
\exists u^H_t\;\forall x\in B_t,\forall u^B_t,\forall w_t:
F(x,u^H_t,u^B_t,w_t)\subseteq \mathcal R.
\]

This condition exposes why BFT cannot create truth from mutually consistent false reports. Sensor diversity, physical redundancy, challenge protocols, secure logging, remote attestation, conservation checks, and active probing are candidate mechanisms. If two world states are indistinguishable to every correct controller but require incompatible safety actions, the invariant is unrealizable from that information state.

### 6.3 Decision closure

The correct coalition must be able to obtain a unique intervention certificate before the belief state exits the recoverable region. Safety requires agreement; liveness requires a synchrony-, connectivity-, and fault-budget-specified route to a decision.

A conservative serial reaction condition is

\[
\tau_{observe}+\tau_{attest}+\tau_{agree}+\tau_{authorize}+\tau_{actuate}
< \tau_{escape}(B_t),
\]

where \(\tau_{escape}(B_t)\) is the minimum adversarial time to force the belief support outside \(\mathcal K\). A sharper theory should model overlapping stages and use reachable sets rather than a scalar sum.

### 6.4 Authority closure

A valid certificate must be sufficient to obtain the required intervention despite Byzantine refusal, and invalid certificates must be insufficient to trigger it.

For a simple \(q\)-of-\(n\) enforcer threshold with at most \(f\) Byzantine signers:

\[
f < q \le n-f
\]

is required to prevent a Byzantine-only coalition from authorizing while allowing the correct coalition to authorize despite withholding. This is only the elementary authorization condition; consensus, correlated ownership, key compromise, coercion of signers, and actuator availability can impose stronger requirements.

Authority should be scoped, expiring, and action-specific. A quorum authorized to quarantine a network endpoint should not thereby acquire unlimited custody over physical persons or unrelated assets.

### 6.5 Actuator closure

Every certified intervention must reach an effector that either:

- correctly executes valid, in-scope commands and rejects invalid ones; or
- is itself replicated, diverse, interlocked, or supervised so that its fault budget is tolerated.

Moreover, invariant-relevant actions should be mediated wherever feasible. This is the world-coupled analogue of a reference monitor: the control mechanism should be non-bypassable for the actions on which the guarantee depends.

Actuator closure can be realized through safety PLCs, hardware interlocks, threshold-controlled keys, command leases, fail-closed valves, circuit breakers, network reference monitors, custodial escrow, site access controls, or human legal/physical enforcement. The implementation changes by domain; the formal requirement does not.

### 6.6 Recovery and continuity closure

Containment must not remove indispensable control capacity. After every authorized exclusion set \(Q\) within the fault model, the remaining system must retain:

- sufficient sensing to estimate invariant-relevant state;
- sufficient actuation to keep the plant in \(\mathcal R\);
- sufficient authority to issue future interventions;
- a specified service floor or a safe degraded mode.

Thus, exclusion and substitution are dual actions. A controller that can be revoked but not replaced is a latent single point of liveness failure. A dangerous physical subsystem may need isolation, but isolation may alter flows elsewhere and create a new unsafe state.

### 6.7 Constitutional closure

The enforcement substrate must itself satisfy meta-invariants. At minimum, a high-consequence intervention should be:

- evidence-linked;
- threshold-authorized or otherwise separation-of-duty-specified;
- scope- and duration-bounded;
- independently auditable;
- reversible where the plant permits reversal;
- reviewable, with a defined reintegration or permanent-exclusion rule.

This is not merely political decoration. A coercive actuator with unconstrained authority is a high-gain controller whose failure can dominate all other fault assumptions. In reflexive B-DIC, police, courts, administrators, root-key holders, safety controllers, and emergency operators are nodes with explicit capabilities and fault budgets.

---

## 7. Candidate theorem and impossibility program

The theory should seek results at least of the following forms.

### Proposition A — Observational indistinguishability impossibility

If two states \(x,y\in\mathcal K\) produce identical correct-controller histories up to the intervention deadline, but every action preserving \(K\) from \(x\) violates \(K\) from \(y\), then no distributed policy can guarantee \(K\) from the corresponding belief state.

**Proof idea:** the correct controllers must select the same action in indistinguishable histories; the adversary chooses the state for which that action is unsafe.

### Proposition B — Unmediated escape impossibility

If a Byzantine actor has an invariant-relevant action \(a\in\mathsf{Cap}_x(i)\) that can force the next state outside \(\mathcal K\) before any correct preemption or compensating action can take effect, then no informational protocol can guarantee \(K\) from \(x\).

**Interpretation:** this is the formal statement behind “the ledger cannot stop the valve.”

### Proposition C — Effective-exclusion criterion

Logical expulsion of node \(i\) preserves safety only if, after reconfiguration:

1. \(i\)’s remaining invariant-relevant capabilities are empty or bounded as tolerated disturbances; and
2. the remaining system retains a safe controller and required service capacity.

This should be sharpened into necessary and sufficient conditions for classes of transition systems.

### Proposition D — Threshold enforcement feasibility

For simple independent signers and a deterministic effector, unauthorized-action safety plus authorized-action availability under \(f\) Byzantine enforcers is possible only when a threshold \(q\) satisfies \(f<q\le n-f\). Variants should treat heterogeneous trust, weighted quorums, mobile faults, adaptive corruption, and multiple actuator domains.

### Proposition E — Recoverability-margin theorem

A delayed distributed intervention preserves \(K\) only from states inside a delay-robust viability kernel. The theorem should relate communication, estimation, authorization, and actuation latency to the geometry of that kernel.

### Proposition F — Recursive enforcement closure

Any unconditional system-level invariant theorem that relies on an external enforcer with invariant-relevant capabilities is incomplete unless that enforcer is proved correct, included in the Byzantine fault model, or explicitly stated as a trusted assumption.

These propositions are individually unsurprising. Their value is in making the trust seams compositional and in connecting distributed-computing impossibility arguments to control-theoretic viability and institutional authority.

---

## 8. Reference architecture

A generic B-DIC architecture has the following control chain:

```text
       WORLD / PLANT / ORGANIZATIONAL STATE
                    |
                    v
   diverse sensing, inspection, attestation, audit
                    |
                    v
        evidence graph + bounded belief state
                    |
                    v
       BFT ordering / fault proofs / certificates
                    |
                    v
 invariant monitor + intervention-policy synthesizer
                    |
                    v
 threshold authority + scoped capability/command lease
                    |
                    v
 digital gates | safety controllers | interlocks | custodians
                    |              |               |
                    +------ physical or legal enforcement -----+
                                   |
                                   v
       WORLD / PLANT / ORGANIZATIONAL STATE

 audit, review, recovery, reconfiguration, and reintegration
 form feedback paths around every layer.
```

The architecture should normally include:

1. **A belief-state estimator** rather than a single accepted sensor value.
2. **A BFT evidence and command service** that separates observations, fault proofs, policy decisions, and actuator receipts.
3. **An invariant monitor or safety-game solver** that computes admissible actions over the current belief support.
4. **A verified baseline controller or safe degraded mode**, following the runtime-assurance intuition of Simplex architectures.
5. **Scoped threshold authorization** whose keys or credentials do not imply broader powers than the intervention requires.
6. **Non-bypassable effectors and reference monitors** for invariant-relevant channels.
7. **Substitution and repair capacity** so exclusion does not collapse controllability.
8. **A constitutional monitor** that treats wrongful intervention, stale emergency authority, and capture of the enforcement layer as invariant violations.

The architectural preference should be to move enforcement toward low-coupling, reversible actions. Filtering a malicious message is preferable to shutting down a plant; revoking an actuator lease is preferable to physically seizing a machine; safe takeover is preferable to punitive removal. Physical force is the residual actuator for capabilities that cannot be technically mediated.

---

## 9. Research program

The research agenda can be partitioned by the mathematical object being produced.

| Program branch | Central question | Expected result class | Decisive failure case |
|---|---|---|---|
| A. Semantics and system boundaries | What counts as state, action, authority, coercion, and effective exclusion? | Formal transition semantics; refinement mappings from BFT and control models | A supposedly external actor retains an unmodeled bypass |
| B. Epistemic resilience | What can correct controllers know under Byzantine sensing and hidden physical state? | Set-membership estimators, active diagnosis, indistinguishability theorems | Correct nodes agree confidently on a false world model |
| C. Distributed safety synthesis | When does a distributed winning policy exist under partial information and deadlines? | Safety-game, barrier, viability, MPC, or supervisory-control synthesis | A safe action exists centrally but cannot be selected from local histories |
| D. Authority and actuator design | How should certificates map to digital, economic, physical, and institutional effectors? | Threshold authorization, capability leases, interlock protocols, actuator-quorum theorems | Valid command cannot compel action, or invalid quorum can compel it |
| E. Dynamic membership and continuity | How can nodes be quarantined, replaced, repaired, and reintegrated without losing safety or service? | Reconfiguration and takeover protocols; degraded-mode contracts | Expulsion preserves integrity but destroys controllability |
| F. Compositionality | When do local invariants and local enforcement imply a global invariant? | Assume-guarantee contracts, graph conditions, compositional barrier certificates | Byzantine nodes violate assumptions on which local proofs depend |
| G. Constitutional meta-control | How is the enforcement substrate constrained and recovered if corrupted? | Meta-invariants, separation of duties, audit and appeal protocols | The safety mechanism becomes the highest-impact attacker |
| H. Benchmarks and evidence | Which testbeds distinguish genuine world control from ledger-only correctness? | Open benchmark suite, fault injectors, assurance cases, comparative metrics | A design “passes” because the actuator or police layer was assumed perfect |

A credible first paper need not solve all branches. A strong initial contribution would combine:

1. one precise B-DIC model;
2. one impossibility theorem showing the consensus-to-control gap;
3. one constructive architecture with an effective-exclusion operator;
4. one nontrivial case study with Byzantine sensors and actuators;
5. one explicit meta-control assumption or mechanism.

---

## 10. Benchmark design

### 10.1 Minimal illustrative benchmark: pressure manifold

Consider a distributed chemical-feed manifold with four controller nodes, multiple pressure sensors, remotely commanded valves, and one manual bypass valve. The safety invariant is

\[
p(t) \le p_{max}.
\]

At most one controller and one sensor may be Byzantine. A BFT service can agree that pressure is excessive and certify “close inlet valve.” Yet safety still fails if:

- the compromised sensor coalition keeps the accepted estimate below the threshold;
- the valve controller ignores the certificate;
- the intervention arrives after the pressure state leaves the recoverable set;
- the expelled controller retains a direct actuator credential;
- closing the inlet disables coolant flow and no replacement policy exists;
- a human operator opens the unmediated manual bypass.

A B-DIC design would add diverse sensing, a set-valued pressure estimate, a verified safety controller, threshold-controlled command leases, fail-closed actuation, actuator receipts, credential revocation, network isolation, takeover by a spare controller, and a physical lock or custodial procedure for the manual bypass.

The manual bypass is the “police” boundary. If any person can open it faster than the enforcement system can intervene, absolute invariance is impossible under a threat model that includes malicious manual operation. The system must either mediate the bypass physically, narrow the adversary model, or weaken the guarantee to probabilistic or damage-bounded resilience.

### 10.2 Benchmark ladder

A broader suite should increase world coupling in specified strata:

1. **Ledger-contained assets:** nearly all relevant capabilities are cryptographically mediated.
2. **Cloud/agent tool system:** APIs and credentials are mediated, but data truth and human side channels remain external.
3. **Microgrid or industrial plant:** irreversible dynamics, sensor and actuator compromise, strict reaction horizons.
4. **Autonomous fleet:** distributed motion, local partial observation, mobile faults, collision and mission invariants.
5. **Multi-organization infrastructure:** legal authority, physical custody, heterogeneous governance, and human enforcement.

### 10.3 Evaluation metrics

Throughput and consensus latency are insufficient. At least the following should be reported:

- robust recoverable-set volume or approximation quality;
- tolerated fault vector \((f_C,f_S,f_A,f_E)\);
- worst-case reaction margin to invariant escape;
- fraction of invariant-relevant actions under complete mediation;
- maximum authority concentration and quorum diversity;
- false-intervention and wrongful-exclusion rates under uncertain evidence;
- service floor after each admissible exclusion set;
- intervention cost and reversibility;
- evidence completeness and independent verifiability;
- recovery and reintegration success;
- assumptions left outside the modeled boundary.

---

## 11. B-DIC domain-analysis instrument

The following canvas is intended for repeated use by researchers, system designers, auditors, or an LLM.

| Analysis field | Required artifact | Diagnostic question |
|---|---|---|
| System boundary | Typed state decomposition \(X_P,X_C,X_I,X_E\) | Which actor, resource, or channel could violate the invariant while remaining outside the state model? |
| Invariant | State predicate or monitor automaton | Is the property safety, liveness, recovery, legitimacy, or a conjunction? |
| Fault model | Domain-specified fault vector and correlation model | What can each Byzantine actor physically and institutionally do, not merely message? |
| Observation model | Local observation maps and belief update | Which relevant states are indistinguishable to correct controllers? |
| Communication model | Authentication, synchrony, partition, and finality assumptions | Can a safe decision be certified before recoverability is lost? |
| Authority model | Roles, certificates, thresholds, scope, expiry | Why does an informational decision bind the intended effector? |
| Actuator model | Effectors, delays, failure modes, bypasses | Which unsafe transitions can still occur after a valid intervention? |
| Intervention set | Typed action algebra with preconditions and effects | Can the system filter, fence, preempt, substitute, sequester, and repair—or only punish afterward? |
| Exclusion semantics | Logical and effective exclusion definitions | What capabilities remain after a node is “removed”? |
| Continuity model | Backup controllers, spare capacity, degraded mode | What invariant or service property fails because the removed node was necessary? |
| Meta-control | Enforcer fault model and constitutional invariant | Who controls the police, root keys, safety controller, and emergency path? |
| Verification target | Theorem, model-checking query, barrier certificate, or assurance case | Which assumptions are proved, tested, monitored, or merely asserted? |
| Counterexample | Minimal adversarial execution | What is the shortest trace in which consensus succeeds but the world invariant fails? |

The final counterexample field is mandatory. It guards against proposals that rename an informational ledger as a controller without closing the actuator path.

---

## 12. Relation to adjacent work and plausible novelty

The proposal is a synthesis, not a claim that every component is new.

Classical Byzantine agreement and practical state-machine replication establish agreement and execution despite arbitrary replica behavior. Byzantine fault-detection and accountability work goes further by producing evidence, isolating faulty nodes, and revoking certificates. These are direct precursors to the evidence and logical-exclusion parts of B-DIC. [R1–R3]

Control-barrier-function and controlled-invariance work treats safety as forward invariance of a safe set. Simplex and runtime-assurance architectures wrap an unverified controller with a verified baseline controller and a switching decision; Distributed Simplex extends this pattern to multi-agent systems under local safety assumptions. Assume-guarantee contracts provide a route from local robust invariant sets to network-level safety. [R4–R6, R9]

Resilient distributed-control work already treats Byzantine or adversarial agents, including constrained consensus and distributed MPC. Runtime shield synthesis and attack-resilient supervisory control explicitly restrict or rewrite unsafe outputs and model sensor/actuator attacks. These are close to the operational-intervention part of B-DIC. [R7–R8, R10]

The plausible unifying gap is narrower and more specific:

> Existing threads generally stop at different boundaries. The B-DIC program makes **dynamic authority, capability reduction, effective exclusion, physical or institutional actuation, replacement capacity, and recursive control of the enforcer** first-class variables in the same invariant-preservation problem.

A targeted literature review did not reveal a canonical field name or a single formalism that closes all of these layers. That should be treated as a research hypothesis, not as a settled novelty claim. A systematic review may find closer work in cyber-physical security, supervisory control, distributed runtime enforcement, institutional multi-agent systems, access-control theory, critical-infrastructure resilience, or formal governance.

---

## 13. Copy-pastable LLM research brief

```text
You are a technical research assistant developing a research program called
“Distributed Invariant Control under Byzantine Conditions” (B-DIC).

OBJECTIVE
Develop a rigorous theory that generalizes Byzantine fault tolerance from
agreement over replicated informational state to preservation of invariants over
an endogenous cyber-physical-institutional system. The controllers, sensors,
actuators, membership rules, authority allocations, enforcement mechanisms, and
repair mechanisms must be modeled as components of the controlled system.

CORE PROBLEM
Given:
  1. a joint state space X containing plant/world state, controller state,
     institutional/authority state, and evidentiary state;
  2. a safety invariant K subseteq X and a separately specified liveness or
     service-floor objective L;
  3. distributed controllers with partial local histories;
  4. a capability-specified Byzantine adversary with domain-specific fault
     budgets for controllers, sensors, actuators, and enforcers;
  5. bounded environmental disturbances and communication/actuation delays;
  6. an intervention set that may alter plant inputs, membership, credentials,
     custody, role assignments, and actors’ future capability sets;
construct or characterize distributed policies that keep every admissible
execution inside K from a robust recoverable set R and satisfy L under stated
additional assumptions.

FIXED TERMINOLOGY
- “Agreement” means consistency of decisions or replicated state; it does not
  imply truth or compliance.
- “Capability” is the state-dependent set of actions an actor can physically,
  digitally, economically, or institutionally realize.
- “Coercive intervention” is a nonconsensual reduction of a target’s effective
  capability set.
- “Logical expulsion” removes protocol membership.
- “Effective exclusion” also removes or bounds all invariant-relevant action
  channels and supplies replacement capacity where needed.
- “Reflexive B-DIC” includes the enforcers and their authority inside the state
  and fault model.
- A “police force” is one possible physical/institutional actuator; it is not a
  trusted oracle and not the generic primitive.

MANDATORY DISTINCTIONS
Do not conflate:
  agreement with truth;
  a certified command with executed effect;
  fault detection with fault proof;
  logical membership removal with effective exclusion;
  punishment with containment;
  containment with substitution or recovery;
  Byzantine behavior with rational utility maximization;
  present safety with membership in a delay-robust recoverable set;
  physical force with complete actuator closure;
  system safety with legitimacy of the enforcement mechanism.

FORMAL OBJECTS TO PRODUCE
1. A typed system model with X, Node, Observation, Action, Disturbance, Safe,
   Cap, Observe, Next, and a fault-admissibility predicate.
2. An extensional execution semantics with distributed policies and arbitrary
   Byzantine strategies within capability envelopes.
3. A robust recoverable set R and a formal solution definition for safety and
   conditional liveness.
4. An intervention algebra containing at least evidence, decision, capability,
   operational, continuity, custodial/physical, repair, and constitutional
   actions.
5. A formal definition of effective exclusion.
6. A theorem or counterexample demonstrating that BFT consensus alone cannot
   guarantee an external-world invariant.
7. At least one constructive architecture linking evidence, BFT certification,
   threshold authority, non-bypassable actuation, safe fallback, replacement,
   and audit.
8. A meta-invariant constraining the enforcement substrate.

RESEARCH QUESTIONS
A. Under what observability conditions does a safe distributed policy exist?
B. How should viability kernels, control barrier functions, safety games, or
   supervisory control be generalized to Byzantine partial information?
C. What authority and actuator-quorum conditions are necessary and sufficient
   for safe and available intervention?
D. When is logical expulsion equivalent to effective exclusion?
E. What replacement and degraded-mode conditions preserve controllability after
   quarantine or removal?
F. When do local invariant contracts compose into a global invariant if some
   components violate their assumptions adversarially?
G. How can the enforcement layer be Byzantine-resilient without an infinite
   regress of trusted controllers?
H. What minimal-intervention objective preserves safety while minimizing
   capability restriction, service loss, irreversibility, and wrongful action?

CANDIDATE RESULTS TO INVESTIGATE
- Observational-indistinguishability impossibility.
- Unmediated-escape impossibility.
- Effective-exclusion criterion.
- Threshold-enforcement feasibility: in the elementary independent-signer
  model, f < q <= n-f.
- Reaction-margin or delay-robust viability theorem.
- Recursive-enforcement closure theorem.
- Compositional local-to-global invariant theorem under adversarially monitored
  assume-guarantee contracts.

REFERENCE ARCHITECTURE
Model the chain:
  world -> sensing/attestation -> bounded belief -> BFT evidence and command
  service -> invariant monitor or policy synthesizer -> scoped threshold
  authority -> digital/physical/institutional actuator -> world.
Add feedback for actuator receipts, audit, recovery, reconfiguration, appeal,
and reintegration. Treat each layer as fault-prone.

DELIVERABLE
Write a 5,000–8,000-word research note or proposal with:
  1. abstract and thesis;
  2. closest prior work and an exact delta, using primary sources;
  3. formal model and assumptions;
  4. at least one impossibility proposition;
  5. at least one constructive architecture;
  6. action and authority taxonomy;
  7. research agenda with theorem, algorithm, and benchmark outputs;
  8. one digital and one cyber-physical case study;
  9. explicit limitations and trusted assumptions;
  10. a compact glossary.

QUALITY CONTROLS
- Label every claim as definition, theorem, conjecture, inference, design
  recommendation, or empirical hypothesis.
- Search for and cite primary work in BFT, Byzantine fault detection,
  reconfiguration, resilient distributed control, controlled invariance,
  runtime assurance/Simplex, shield synthesis, supervisory control under
  sensor/actuator attacks, capability security, and institutional multi-agent
  systems.
- Do not claim novelty from absence of a familiar label.
- For every proposed guarantee, identify the exact observation, timing,
  authority, actuator, jurisdiction, and recovery assumptions.
- Include the shortest counterexample in which consensus succeeds while the
  world invariant fails.
- Never place “the police,” “the administrator,” “the safety controller,” or
  “the hardware root” outside the model without marking it as a trusted base.
```

---

## 14. Conclusion

The police intuition points to a real missing layer, but “police” is too implementation-specific to be the primitive. The generic primitive is **effective control over invariant-relevant capabilities**. That includes the capacity to restrict, preempt, transfer, or remove agency and the capacity to replace the function that was removed.

The research object is therefore not a ledger plus sanctions. It is a reflexive distributed controller whose evidence, decisions, authority, effectors, enforcement, and recovery paths are all Byzantine-specified and whose success criterion is trajectory-level invariance of the system that contains them.

A compact formulation is:

> **BFT coordinates beliefs and commands. B-DIC closes the loop from contested evidence to bounded authority to effective world intervention, while keeping both the plant and the enforcer inside the invariant.**

---

## References

**[R1]** Leslie Lamport, Robert Shostak, and Marshall Pease. “The Byzantine Generals Problem.” *ACM Transactions on Programming Languages and Systems*, 4(3), 1982. DOI: 10.1145/357172.357176.

**[R2]** Miguel Castro and Barbara Liskov. “Practical Byzantine Fault Tolerance.” *OSDI*, 1999, pp. 173–186.

**[R3]** Andreas Haeberlen, Petr Kouznetsov, and Peter Druschel. “The Case for Byzantine Fault Detection.” *HotDep*, 2006.

**[R4]** Aaron D. Ames, Xiangru Xu, Jessy W. Grizzle, and Paulo Tabuada. “Control Barrier Function Based Quadratic Programs for Safety Critical Systems.” arXiv:1609.06408; later *IEEE Transactions on Automatic Control*.

**[R5]** D. Seto, B. Krogh, L. Sha, and A. Chutinan. “The Simplex Architecture for Safe On-Line Control System Upgrades.” *American Control Conference*, 1998. DOI: 10.1109/ACC.1998.703255.

**[R6]** Usama Mehmood, Scott D. Stoller, Radu Grosu, Shouvik Roy, Amol Damare, and Scott A. Smolka. “A Distributed Simplex Architecture for Multi-Agent Systems.” arXiv:2012.10153, 2020.

**[R7]** Xuan Wang, Shaoshuai Mou, and Shreyas Sundaram. “Resilience for Distributed Consensus with Constraints.” arXiv:2206.05662; *IEEE Transactions on Automatic Control*, 70(10), 2025.

**[R8]** Yu Wang, Alper Kamil Bozkurt, Nathan Smith, and Miroslav Pajic. “Attack-Resilient Supervisory Control of Discrete-Event Systems: A Finite-State Transducer Approach.” arXiv:1904.03264, 2019.

**[R9]** Yuxiao Chen, James Anderson, Karan Kalsi, Aaron D. Ames, and Steven H. Low. “Safety-Critical Control Synthesis for Network Systems with Control Barrier Functions and Assume-Guarantee Contracts.” arXiv:1911.03452, 2019.

**[R10]** Roderick Bloem, Bettina Könighofer, Robert Könighofer, and Chao Wang. “Shield Synthesis: Runtime Enforcement for Reactive Systems.” *TACAS*, 2015. DOI: 10.1007/978-3-662-46681-0_51.

**[R11]** NIST. “Reference Monitor.” *Computer Security Resource Center Glossary*. Definition derived from NIST SP 800-53 Rev. 5.
