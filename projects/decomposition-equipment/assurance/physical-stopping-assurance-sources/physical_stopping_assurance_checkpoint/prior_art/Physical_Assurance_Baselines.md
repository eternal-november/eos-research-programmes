# Physical stopping assurance: baseline and significance audit

29 October 2026. Primary-source comparison; not a novelty clearance. Prepared against the completed reusable-environment-discovery and safety-representation-discovery milestones.

## Plain-language abstract

Making a learned predictor support a real braking controller is worthwhile, but it enters a mature field. Existing methods already combine uncertain models, safety monitors, backup controllers, sampled sensing, actuation delay, and stopping-distance calculations. Our earlier work also already included a stopping example and the conversion of a predictive error bound into a risk bound. Therefore the next result should not claim that this combination is itself new.

The useful additional burden is more specific: discover from records which signals, shared uncertainties and memory must be retained; turn that discovered representation into a controller that can actually obtain and use those signals on time; and prove that its physical safety conclusion survives the implementation. The result must say which physical facts still need engineering evidence. A proof that depends on calibrated distance, adequate braking and a reliable emergency path does not establish those facts merely by fitting observation records.

## 1. Prior internal results that must not be counted twice

`/workspace/shared/safety_representation_discovery_20261029/theory/Causal_Evidence_and_Risk_Decomposition.md` already separates a physical upper hazard envelope from the observable risk event. Its stopping example combines delay and braking effects, and shows why separately measured marginals can fail to establish the risk of their conjunction. An observer-search example already discovers a joint Boolean report. This is a useful predecessor, not new work for the present milestone.

`/workspace/shared/reusable_environment_discovery_20261029/theory/Discovery_and_Reuse.md` already provides unknown predictive-scope discovery, recursive memory minimization, shared-source groups, and feedback-uniform stopped-transcript guarantees, conditional on its declared model family and coverage. `Witnessed_Feedback_Composition.md` already treats executable common responses and permitted local encodings. These do not establish a physical robot model, a braking envelope or hard real-time implementation.

## 2. Closest primary baselines

### Stopping distance and response time

Shalev-Shwartz, Shammah and Shashua, [On a Formal Model of Safe and Scalable Self-driving Cars](https://arxiv.org/html/1708.06374v6), Definition 1 and Lemma 2, derive longitudinal safe distance using response time, possible acceleration before reaction, and lower/upper braking bounds. A stationary obstacle is a straightforward specialization. Thus adding acceleration during sensing/communication delay to the familiar braking formula is baseline mechanics, not a new decomposition theorem. The source also explicitly discusses occlusion; a claim of novelty merely from considering unseen obstacles would be inappropriate.

### Runtime assurance and verified braking

Johnson, Bak, Caccamo and Sha, [Real-Time Reachability for Verified Simplex Design](https://doi.org/10.1145/2723871), use a trusted switching mechanism and safety controller to protect execution of an unverified controller, including embedded implementation. The essential question is whether continuing with the advanced controller preserves recoverability, not whether an emergency command can be issued after danger is detected.

Slagel and colleagues, [A Formal Verification Framework for Runtime Assurance](https://ntrs.nasa.gov/citations/20240006522), formalize Simplex using hybrid programs in PVS and illustrate it on automatic vehicle braking. The inspected NASA record is a presentation accompanying the 2024 work; this audit relies on its stated scope, not an uninspected detailed theorem.

Mehmood and colleagues, [Black-Box Simplex / Safe CPS from Unsafe Controllers](https://arxiv.org/html/2102.12981v1), replace static verification of the baseline controller by runtime checking of safe command sequences. Definition 3 requires safety recovery after a command for every admitted disturbance. A learned or unverified fallback is therefore not by itself new either: what matters is the soundness and timely execution of its check, and availability of an already validated continuation.

### Sampled sensing, delay and intersample safety

Singletary, Chen and Ames, [Control Barrier Functions for Sampled-Data Systems with Input Delays](https://arxiv.org/html/2005.06418v1), establish sampled-data invariance with state uncertainty and delayed actuation. Section IV assumes delay is a known integer multiple of the control period, retains input history, and requires the initial uncertainty set to remain safe before the first action can take effect. These qualifications are directly relevant: a freshness check made only at controller ticks cannot justify ignoring the interval until the next tick or the actuator pipeline. An input-history buffer is a standard implementation necessity, not necessarily discovered physical structure.

Zhang, Walters and Xu, [Control Barrier Function Meets Interval Analysis](https://arxiv.org/abs/2110.00915), treat sampled-data safety with measurement and actuation uncertainties using reachable-set overapproximations, including quadcopter experiments. Merely reporting robust sensor/actuator intervals and simulation would be weaker evidence of physical implementation than this baseline.

### Learning and predictive certificates already support safety filters

Wabersich and Zeilinger, [A Predictive Safety Filter for Learning-Based Control of Constrained Nonlinear Dynamical Systems](https://arxiv.org/html/1812.05506v3), combine a data-inferred uncertain dynamics model with online safety filtering and backup plans to a terminal safe set. If a fresh plan fails, an earlier certified continuation is used. This is the close baseline for learned prediction plus fallback safety; the proposed milestone must identify what its representation discovery adds, rather than contrast against only perfect-model controllers.

Coppola, Peruffo and Mazo, [Data-Driven Abstractions for Control Systems via Random Exploration](https://arxiv.org/abs/2402.10668), build abstractions from finite trajectories with PAC probabilistic alternating-simulation guarantees supporting controller refinement. Our earlier audit examines its qualifications in detail. Consequently neither learning an abstraction from readouts nor formally refining its controller is alone a novel direction.

The 2025 [Data-Driven Input-Output Control Barrier Functions](https://doi.org/10.1109/LCSYS.2025.3569701) specifically constructs invariant-set-based filters for discrete-time LTI systems from input-output data without requiring precise system order or explicit state estimation. Its abstract assumes a noise-free dataset. Discovery claims should distinguish unknown physical dynamics from unknown compositional ownership, stochastic dependence, and executable local memory.

Recent [Conformal Reachability for Safe Control in Unknown Environments](https://arxiv.org/html/2602.03799v1) and [Robust Conformal Prediction for STL Runtime Verification under Distribution Shift](https://arxiv.org/html/2311.09482v2) further establish that statistical uncertainty joined with reachability or temporal-property prediction is an active baseline. These sources were inspected for scope, not exhaustively theorem-audited; they must not be used to claim that all feedback/calibration difficulties are solved.

### Compositional assumptions and guarantees

Kwiatkowska, Norman, Parker and Qu, [Assume-Guarantee Verification for Probabilistic Systems](https://www.prismmodelchecker.org/papers/tacas10.pdf), give compositional quantitative verification for probabilistic automata, including asynchronous interaction and circular rules. The related [learning-based framework](https://www.prismmodelchecker.org/bibitem.php?key=FKP10) automatically learns assumptions using model-checker queries. Thus automatic interface-contract synthesis is not an empty prior-art category. Our distinction is observational discovery of sufficient interfaces and joint stochastic realization, not simply writing local assumptions that imply a global safety theorem.

## 3. What would make the new milestone substantive?

These are proposed acceptance burdens, not claims of achieved novelty:

1. **Representation is genuinely discovered.** Begin with action/readout evidence and a declared vocabulary/physical envelope, not the final braking-state machine, sufficient sensor subset or shared-source grouping. Output candidate scopes, recursive memory and joint source dependencies, with a stated validity domain.
2. **A representation choice changes what can be certified.** Exhibit two evidence-compatible alternatives that agree on discarded reports but require distinct admissibility judgments. Then show which additional joint report or memory resolves the ambiguity. More telemetry cannot be treated as free, and unmeasured correlations cannot be manufactured.
3. **The executable implementation refines the discovered semantics.** Specify timestamp origin, clocks and uncertainty, message identity, sampling, deadlines, computation, action holding, brake latency, and stale/reordered/missing-data behavior. Charge memory, communication, randomness and worst-case computation separately.
4. **Fallback is guaranteed before it is needed.** At permission time preserve a stopping reserve until the next possible intervention, including expiry and queue delays. A missing message can trigger a local watchdog only if that watchdog and its path to the actuator retain the promised availability. Failure of the very brake channel used by the fallback is not solved by sending another stop packet.
5. **The physical event is justified.** A transcript-level event must soundly dominate collision or unsafe entry under explicit geometry, distance/speed error and dynamics assumptions. Moving obstacles and occluded entrants require their own assumptions; stopping before a static boundary is not universal collision avoidance.
6. **Quantitative claims retain their quantifiers.** Separate training-confidence failure, deployment failure probability, prediction approximation, coverage exit and physical-envelope failure. The same closed-loop policy, initialization and sensing schedule must be covered by the predictive theorem. Repeated use does not yield an infinite-horizon claim for free.
7. **Utility is demonstrated rather than stipulated.** Compare against a worst-case robust stop/no-entry baseline. Report certified additional entries/progress as well as risk. If stopping immediately always passes, that is safety but not useful decomposition discovery.

## 4. Scope recommendation and honest significance language

A plausible claim is: “A constructive, quantitatively checked bridge from discovered predictive components to a timed stopping controller, with explicit evidence and implementation obligations.” It should not yet be called a new general theory of physical assurance or unique architecture identification.

The physical envelope can legitimately remain a declared premise. The report should enumerate which parts are learned, measured by separate calibration, established by design, checked online, or simply assumed. The scientifically interesting question is how much relevant representation can be discovered under that premise and whether the certificate is preserved by its executable implementation.

This audit does not establish that the combined discovery-to-execution theorem is absent from the literature. A final novelty comparison must use the actual theorem and hypotheses after the proof and example stabilize. The baseline is sufficiently strong that a synthetic successful stopping calculation, without the discovery and implementation obligations above, would primarily be an integration demonstration.
