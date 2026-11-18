# Byzantine-resilient distributed invariant control

Status: design formulation and motivating example, sharpened from the user’s clarification of the intended problem. The empirical examples below are stipulated scenarios, not claims about an actual deployment. The existing proofs retain their stated scopes; this document does not claim a solution to the community scenario. It makes independent actuation, limited local information, physical counterintervention, and fallible enforcement defining requirements.

The problem asks when a population of independently controlled, heterogeneously capable participants can preserve specified constraints on a shared evolving world despite adversarial deviations. A replicated computation can be one mechanism within that population. No protected global execution gate is assumed to mediate all consequential actions.

## A community with no trusted global controller

Residents, businesses and public organizations independently own and operate pumps, floodgates, environmental sensors, inspection drones, autonomous vehicles and equipment capable of containing or interfering with other devices. Ownership, technical access, institutional authority and actual physical influence do not coincide. No participant has a complete view of the water network, and no central controller has reliable, exclusive control over every actuator.

For a declared envelope of storm conditions, the mission protects occupied upstream and downstream districts from dangerous water conditions while maintaining essential drainage and service. Permanent shutdown, forced abandonment of the community or relabeling an occupied district does not discharge that mission by bookkeeping.

During a storm, a privately operated floodgate releases water toward an occupied district. Its controller reports that the release is safe. Other instruments indicate a growing hazard. The disagreement might reflect a defective transducer, deliberate deception, stale observations, different hydraulic models, or measurements of different parts of the network. Several apparently independent reports might share a compromised calibration source or communications link.

An inspection drone can obtain additional evidence, but its own observations, position estimate, calibration and reports may also be unreliable. Observing the gate’s visible position does not establish the flow through a concealed bypass. Authenticity of a signed report does not establish truthful content, calibration, or the adequacy of its prediction model. The available evidence must support an intervention before the physical deadline; attribution obtained afterward may be useful for accountability but cannot prevent that flood.

Even a correct collective assessment does not compel the gate to stop. Its controller can ignore a legitimate instruction and continue operating equipment it controls directly. The owner might be malicious, mistaken, or sincerely applying another model. Other participants may be able to reduce the inflow, divert water, protect a district, evacuate people, constrain the actuator’s movement, isolate its power or access, or physically disable it. Some interventions could involve seizure or irreversible destruction. Each possibility requires a declared capability, delay, resource cost and effect relation; none follows from a vote or a permission record.

Counterintervention can make matters worse. Closing the suspect gate can transfer danger upstream. Disabling a pump can remove indispensable drainage or essential service. Two individually plausible diversions can overload the same receiving channel. A malicious participant can fabricate evidence to induce a destructive response against a functioning device. Equipment assigned to enforcement can itself refuse, deceive, overreach, or act independently of the collective decision.

The community therefore needs more than a rule for deciding whose report to believe. It needs to determine whether one family of locally implementable policies can maintain the joint safety constraints, preserve an essential-service floor, and keep its prescribed responses admissible against the declared attacks. The downstream district, upstream district, operators, property holders and service recipients have distinct interests. For the first research layer, the rules combining those interests are stipulated explicitly; their legitimacy is not inferred from successful control.

The joint state must retain the consequences of enforcement: changes in flow, remaining capacity, damaged or occupied equipment, access rights, communication and sensing opportunities, pending effects, resource depletion and any history needed to evaluate duties or justification. An intervention that prevents today’s flood by deleting tomorrow’s indispensable control capability can fail the mission.

The same problem can concern a person’s safety, a facility, an information system or an institutional relationship. Flood control is the motivating instance, not the definition of the problem.

## The semantic requirement the example fixes

Classical Byzantine state-machine replication can implement arbitrary deterministic application logic. Its guarantee concerns the replicated behavior under its fault and communication assumptions. Application logic describing a shutdown does not, by itself, stop a machine that retains an independent path to the world.

For this problem, agreement is neither sufficient nor universally necessary. Participants can agree on a false state; agree on a true state but lack timely influence; or maintain safety through compatible local interventions while retaining different beliefs. The required epistemic condition is decision-relevant information, not complete reconstruction or universal knowledge of a violation. A common safe response can exist even when the underlying state remains ambiguous.

The example has five load-bearing features: independently exercised capabilities, potentially conflicting local information, adversarial physical effects, counterintervention that changes those capabilities, and admissibility constraints on counterintervention itself. A simplification preserves the motivation only if these distinctions continue to affect some judgment or outcome. Introducing a protected gate that prevents every unauthorized effect would remove the central case. Such a model remains useful as a comparison or a deliberately trusted-interface subcase.

“No trusted global controller” does not mean “no assumptions.” Physical laws, capability limits, initial resources and surviving mechanisms need explicit models. Every claimed residual protection must state what enforces it, which failures it survives and which attacks remain admitted. A named component cannot be exempted from the fault family merely because its correctness would finish the proof. Independently justified physical restrictions or bounded failure assumptions are possible outcomes, but their contribution must remain visible.

## Mathematical kernel and the first research layer

Fix a context θ containing the actual plant/model uncertainty, identities and component ownership, primitive capability interfaces, observations, communication, timing, initial scenarios, fault dependencies, intervention rules and required service. A state z can contain continuous physical variables, discrete apparatus modes, institutional records, queues, resources and sufficient history. Local model states need not equal the actual plant parameter.

Use a joint transition relation

\[
z_{t+1}\in F_\theta(z_t,a_{1,t},\ldots,a_{n,t},w_t)
\]

and local observations

\[
o_{i,t}\in O_{i,\theta}(z_t,\rho_{\le t},f).
\]

The move order and causal information available to the adversary are part of θ. Actions can modify the world, another participant’s apparatus, the observation network or future intervention capabilities. Thus the system is a feedback network whose interfaces can change, not a fixed pipeline from consensus to a passive actuator.

Let f range over a joint fault family \(\mathfrak F_\theta\) on actual components, including independently compromisable sensors, links, clocks, keys, policy executors and enforcement devices. The set C(f) identifies policy executors required to follow their prescribed programs. Fault sets for particular roles are projections of this same f; they do not establish statistical independence. A participant with an uncompromised planner can still have a compromised sensor or actuator, represented in the observation/effect relation.

For deterministic policies \(\pi_i:H_i\to A_i\), the synthesis target is the following schematic judgment:

\[
\begin{aligned}
\exists\pi\in\Pi_\theta^{\mathrm{local}}\;\forall f\in\mathfrak F_\theta\;
\forall \sigma_f\;\forall\eta\;\forall \xi_0\in\mathcal I_\theta(f):\qquad&
\operatorname{Runs}_\theta(\xi_0,\pi_{C(f)},\sigma_f,\eta)\ne\varnothing,\\
&\forall\rho\in\operatorname{Runs}_\theta(\xi_0,\pi_{C(f)},\sigma_f,\eta):
\Phi_\theta^f(\rho).
\end{aligned}
\]

Here \(\sigma_f\) contains admitted causal deviations, including compromised measurement/communication operations and independent actuation; η contains the admitted environmental and scheduling choices. For every admitted f, the initial family is nonempty; impossible fault cases are explicitly excluded rather than counted as vacuous coverage. Initialization includes the participants’ actual initial information. The policy is selected before f. A pointwise winning physical state need not yield a winning initial information family.

For the community example, instantiate

\[
\Phi_\theta^f=
\Phi_{\mathrm{downstream}}\land
\Phi_{\mathrm{upstream}}\land
\Phi_{\mathrm{service}}\land\Phi_{\mathrm{protectedRights}}\land
\Phi_{\mathrm{responseAdm}}^f.
\]

The protected-rights conjunct contains the stipulated world-level constraints on injury, property, disabling essential infrastructure and other protected interests; its violations count regardless of whether an ordinary participant or an enforcer causes them. It is not limited to the conduct of compliant agents. Which rights and justified exceptions it encodes is part of the fixed first-layer specification, not a conclusion of the controller theorem.

The last conjunct evaluates responses prescribed and issued by the compliant policy executors C(f), including their relevant aggregate consequences, under the stipulated authority and conduct rules. Compromised-actuator deviations remain part of the adversarial effect semantics; a compliant planner does not make its independently compromised actuator compliant. Individually permitted interventions can still be jointly inadmissible. If an action/historical property is presented as a state invariant, the state must include its actual monitor update or history; an unattached Boolean “lawful” flag is not a certificate.

Normative prohibition does not remove a Byzantine action from the physical transition relation. Restricting that relation requires an actual capability restriction. Global physical safety, the selected protected-rights constraints and service must survive effects from faulty participants and faulty enforcement devices alike. A malicious enforcer's unjustified seizure cannot be ignored merely because that enforcer is absent from C(f). If its admitted capabilities make that protected outcome unpreventable, the corresponding mission is unrealizable.

A stronger interpretation—every act of every participant must always be lawful—is a distinct mission. If an admitted Byzantine participant can directly perform a forbidden act before anyone can prevent it, that mission is unrealizable. Reporting this obstruction is preferable to silently deleting the attack or silently substituting correct-party compliance. Likewise, an intervention’s institutional validity, its permission, its evidential justification and its physical effect are separate judgments.

Nonblocking applies to every admitted action profile following the correct components. Deadlock, timeout and maximal finite runs receive explicit mission verdicts. Service is specified with its time scale and delivery meaning; permanent shutdown does not pass merely because one instantaneous hazard disappears. Continuous models additionally owe existence of trajectories, intersample safety and a non-Zeno argument.

Randomized controllers require a separately declared almost-sure or quantitative objective and adversary access to randomness. They are not covered merely by writing a deterministic policy as a probability distribution. Finite representation, computable implementation and bounded runtime are also separate burdens from semantic strategy existence.

## A precise information–intervention obstruction

The useful obstruction is about the complete intervention decision through a deadline, not just equal observations at the present instant. Fix a candidate local policy and two admitted causal scenarios with the same component fault scenario f, hence the same compliant-executor set C(f), and the same honest private inputs and law of honest randomness. Include every permitted communication, inspection, challenge and active probe before deadline τ.

Let \(V_0,V_1\) be the joint honest intervention transcripts through τ. Suppose there is a coupling of the execution laws generated by these two admitted causal scenarios, with the required marginal laws, for which \(V_0=V_1\) almost surely. Suppose success in scenario j requires \(V_j\in D_j\), where the measurable sets satisfy \(D_0\cap D_1=\varnothing\). For example, one world requires containment by τ, the other requires retaining the device’s essential function, and no permitted alternative or contingent intervention serves both.

Then

\[
\Pr_0(\mathrm{success})+\Pr_1(\mathrm{success})\le1.
\]

The proof is a direct coupling argument: on the common transcript, both success events cannot occur. One scenario therefore has success probability at most one half; in particular both cannot have probability-one success. The deterministic case is the corresponding identical-action contradiction. To refute every local controller, establish this obstruction for every candidate policy, with causal scenario choices; one pair of histories from one unsuccessful policy is insufficient.

A positive-mass indistinguishable coupling event also defeats probability-one success; a single exceptional random tape need not. Equal marginal observation distributions for each actor do not suffice when their joint correlations differ. The analytical coupling does not grant the adversary future random bits. If faulty sets differ, identities correct in only one scenario require a separate compatibility argument.

This is a sufficient obstruction, not a complete characterization. A timely admissible probe can invalidate the indistinguishability premise for a policy that uses it. This removes that obstruction only; it does not establish sufficient control authority, admissible responses, or successful service. A response safe in both worlds, a changed physical capability arrangement, or a changed mission can also remove a premise. These are routes to reconsider feasibility, not sufficient feasibility conditions. More replicas or authentication help only if they supply a material change of this kind. An inspection that finishes after τ does not remove the obstruction.

A second, independent obstruction is insufficient causal authority. If an adversary can force an unsafe transition through an unopposed physical channel, more accurate beliefs alone cannot win. Conversely, adequate physical capacity can fail to be usable because local information or admissibility constraints prevent selecting it. These three conditions must be checked jointly.

## Fault coverage derived from the model

A comprehensive classification needs a declared universe. Here the universe is the typed feedback network represented by θ. For each primitive interface p, record its nominal relation \(R_p\), admitted adversarial replacement relations, timing and resource effects. Classify an attack by every interface it controls or violates. A joint failure can also occur while every local interface satisfies its own contract; record that as a composition or specification failure with its interaction witness, rather than inventing a faulty component. The coordination and specification rows retain this case. The rows below are interface families, not mutually exclusive causes and not a universal list of everything that can go wrong.

| Interface family | Failure or adversarial behavior | Motivating diagnostic and affected judgment |
|---|---|---|
| Initial configuration and resources | Wrong deployment state, preexisting damage, exhausted reserves or compromised startup material. | A correct response starts too late or lacks the capacity assumed by a proof; initial winning-family membership changes. |
| Observation production | Incorrect sampling, calibration/pose error, occlusion, substituted readings, false time alignment or missing measurements. | Visible gate position and actual bypass flow disagree; state/evidence coverage fails. |
| Inspection and attestation | Compromised witness, colluding inspector, misleading provenance, or a probe that changes/damages its target. | A drone appears to corroborate a sensor while sharing its defect; purported independent evidence is not independent. |
| Communication and identity | Equivocation, omission, replay, selective delay, misrouting, credential misuse or feasible forgery. | Different defenders receive incompatible apparently current instructions; local histories and coordination change. |
| Representation and inference | Corrupted estimator/model/update, suppressed uncertainty or malicious inference software. | Identical truthful measurements feed different hydraulic assumptions; distinguish admitted uncertainty from a false model guarantee. |
| Decision and coordination | Wrong command, withholding, incompatible reservations or jointly harmful individually plausible decisions. | Two defenders divert water into the same constrained basin; local correctness does not establish joint safety. |
| Physical realization | Uncommanded actuation, refusal, inversion, delayed/duplicate effects, bypass paths or resource saturation. | A privately controlled gate ignores an authenticated shutdown; command agreement does not imply effect. |
| Counterintervention and containment | Malicious or mistaken targeting, ineffective isolation, excessive intervention, or interference among enforcers. | Disabling a suspect pump removes required drainage; enforcement is itself an attack surface. |
| Timing and scheduling | Skew, stale evidence, missed response windows, starvation or unbounded zero-time protocol activity. | A correct inspection completes after the flood can no longer be prevented; safety and service clocks diverge. |
| Authority and recognition | Forged records, abuse of valid power, incorrect permission inference or changes not recognized by other participants. | A genuine credential is used for an impermissible seizure; credential validity does not supply permission or effect. |
| Repair and reconfiguration | Incomplete repair, contaminated keys/state, lost commitments, false readiness or unsafe reintegration. | A repaired actuator resumes an old harmful command; fault interpretation and physical history cannot be reset by naming a new epoch. |
| Specification and its governance | An inadequate reference objective, manipulated interpretation, or dishonest change through a modeled rule-revision interface. | A controller “succeeds” by redefining occupancy or authorizing its own abuse; distinguish a defective governing specification from an attack within an adequate one. |

Every classification also records coalition/support and common causes; deviation mechanism; onset, duration and persistence; adversary knowledge and resources; detectability and recoverability; and the violated safety, service or normative judgment. Numeric sensor error within its declared bound and legitimate disagreement between honest models are admitted uncertainty, not automatically faults. Malice is not a necessary explanation of an observed deviation. “Arbitrary Byzantine behavior” means arbitrary causal behavior within the declared physical and informational capabilities, not unlimited power over physics.

A formal instance must assign every primitive interface, including initialization and interface-changing operations, to this classification or explicitly extend it. Exhaustiveness is conditional on checking that assignment and the model boundary; the present narrative does not complete that inventory. Given the checked assignment, coverage follows only for interfaces represented in θ: every represented departure has one or more such locations. The classification neither establishes that θ includes every real attack channel nor licenses independent per-row fault budgets. A newly discovered channel or an unmodeled cross-interface dependency reopens the model and its taxonomy. The specification-governance row deliberately has two cases: adequacy failures outside the chosen specification, and adversarial rule-changing acts represented inside it.

The example set should cover interactions, not just one example per row. The watershed scenario covers a sensor-to-enforcement false-accusation chain, refusal after agreement, unsafe counterintervention and conflicting defenders. Complement it with the following abstract scenarios; none is a deployment design or a solved benchmark.

| Further scenario | Material combination it adds |
|---|---|
| A care system with independently controlled monitoring and delivery devices | A compromised device creates a hazard; isolation removes an essential service, while observations and consent/authority differ. This tests individual safety and intervention admissibility without making a social aggregate the only protected object. |
| Mobile robots sharing a constrained workspace | A malicious mover obstructs others; containment consumes space and agent capacity, and a mistaken capture can itself create danger or permanent blockage. |
| A shared information system with several independent write/access paths | A replicated audit log agrees while a privileged endpoint changes the protected resource outside that log; revocation, repair and historical evidence have different scopes. |
| An institutional process with fallible inspectors and decision makers | Genuine powers can be abused, evidence can be fabricated to induce intervention, and a rule revision can alter whose interests count as protected. Fixed-rule enforcement and governance of those rules must remain separate. |

Together these scenarios illustrate the listed interface families and selected couplings. They are not an exhaustive enumeration of their combinations. Each future formal benchmark should identify its covered rows, joint attacks, omitted channels and discriminating continuation tests. A benchmark that silently restores a protected global gate fails the current motivation’s central coverage test.

## Existing foundations and bounded novelty claim

The proposed synthesis must build on adversarial control, secure estimation, decentralized supervision and distributed games. A claim that no previous work addresses malicious physical agents would be false. The potential contribution is an explicit account of their combined assumptions, feasibility conditions and composition, including untrusted counterintervention and authority. Whether a particular new theorem or combined subclass is novel remains a separate literature question.

The following primary-source checks were made on 2026-10-22. A check mark is limited to the stated inspection; none denotes a completed local import or exhaustive search.

| Primary source | Checked scope and consequence |
|---|---|
| [Usevitch–Panagou, arXiv:2102.05014v1](https://arxiv.org/html/2102.05014v1) | [✓] §II-A, Remarks 3–4; Theorems 2, 3 and 5 and their hypotheses. Heterogeneous sampled control against adversarial inputs is substantive prior art. This version assumes known adversarial identities and sampled full-state information, bounded inputs/disturbances, and feasibility or additional best-effort conditions. An always-feasible optimization is not unconditional safety. It does not establish the combined unknown-fault, unreliable-observation and constrained-enforcement case here. Statements checked; proofs not independently reconstructed. |
| [Ashkenazi et al., Forgive & Forget, CANDARW 2019, author-uploaded text](https://www.researchgate.net/publication/338509594_Forgive_Forget_Self-Stabilizing_Swarms_in_Spite_of_Byzantine_Robots) | [✓] §II and Lemmas 2–3. In a synchronous full-visibility grid model, even faulty robots obey adjacency and occupancy constraints; stationary correct neighbors can block their movement. Specific ring/board constructions combine containment with recurring cleaning. This supports model-level physical counterintervention, not demonstrated hardware restraint. The related [journal article](https://doi.org/10.1002/cpe.6123) was checked only at abstract/bibliographic level [✓]; its theorem-level text remains uninspected [~]. Do not confuse the conference full text with the journal version. |
| [Rudie–Wonham, Think Globally, Act Locally, 1992, author-uploaded text](https://www.researchgate.net/publication/3021210_Think_globally_act_locally_decentralized_supervisory_control) | [✓] Abstract, global/local control formulation and §§III–IV, including the controllability/coobservability solvability statements. Decentralized supervisors for global legal behavior are a direct predecessor. Their event-control, observation and decision-composition interfaces must be matched to actual participants and physical intervention; a mathematical disabling authority cannot silently become a universal physical kill switch. This is a scoped source comparison, not a new import proof. |
| [Schewe, Distributed synthesis is simply undecidable, accepted manuscript](https://www.researchgate.net/publication/259090125_Distributed_synthesis_is_simply_undecidable) | [✓] Classical synchronous architecture setting, Theorems 3.3, 4.4 and 5.1: even restricted safety/reachability specification languages retain an undecidability boundary. This does not make every fixed architecture or bounded controller search undecidable. [Finkbeiner–Schewe’s author record](https://finkbeiner.groups.cispa.de/publications/2005-uniform-distributed-synthesis/) [✓, abstract-level] supplies the architecture-sensitive comparison. The local task needs stated subclasses and effective representation assumptions. |

Search coverage was targeted to these source families and their load-bearing assumptions. Direct publisher routes for some texts were inaccessible; accepted manuscripts and identifiable author uploads supplied the inspected versions. This check establishes substantial predecessors and exact comparison duties, not a claim that the combined frontier is unoccupied. Reopen literature work before selecting a new theorem, asserting optimality or claiming novelty for a specific combination.

## Bounding the next research step without deleting the problem

Hold the mission and authority rules fixed first. Keep their justification and revision as a separate governance problem. Under fixed rules, local enforcement can be technically successful yet fail a broader stakeholder law if the chosen specification is defective; a theorem about the fixed rules does not adjudicate that law. Later work may make rule interpretation, recognized powers and revisions part of the adversarial dynamics, with its own constraints on legitimate change.

A bounded first target should exhibit which combinations of observation coverage, physically enforceable influence, counterintervention capacity and response latency admit a distributed strategy for the same world safety and service objective. Candidate answers are a controller with a checked invariant and realization law, an exact characterization in a stated class, or a legal indistinguishability/capability obstruction at the requested scope. A failed bounded search is none of these by itself.

The defining positive benchmark must include independently exercised physical effects, an unknown joint fault scenario that can include enforcement components, and consequential constraints on the defenders’ responses. It may bound the plant, fault count, topology, horizon and capabilities. It must not obtain its result by exempting a universal execution authority from the very fault coverage at issue. A comparison using protected interfaces can expose the cost of removing that premise, but cannot substitute for the defining result.

For a useful test family, vary information, physical authority and latency while holding the mission and other interfaces fixed. Include scenarios in which additional timely observation changes feasibility, correct knowledge still lacks adequate influence, and a powerful countermeasure is excluded by the joint admissibility requirement. These cases identify why a controller succeeds or fails. The same policy must preserve required service; the alleged safety solution cannot permanently disable the community.

## Relation to the existing checked package

The general execution carrier, unknown-fault policy quantification, compatible continuation construction, local refinement laws and existing obstructions in [research/PROGRAM.md](research/PROGRAM.md) remain useful. Their reuse requires the new fault, capability, observation and time interfaces to be instantiated.

The protected-gate physical and recovery constructions remain conditional results. Their fault families exclude the actuator/service roots, gate, isolation interface, schedule publisher, key installer and office described in their specifications. They therefore do not establish the present defining case involving fallible enforcers and independent actuation outside a protected global gate. The earlier completion audit is retained as evidence about its audited family, not as a verdict that this clarified intended problem is solved.

This document changes the formulation and the interpretation of completion, not the old proof statements. The previously hashed handoff packet and executable evidence remain unchanged so their reproduction can still be checked against the original snapshot. The active entry point is the [subproject TODO](TODO.md), which carries the remaining design obligations and distinguishes them from mathematical checking of the earlier package.
