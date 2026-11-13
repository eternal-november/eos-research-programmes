# Recovered environmental applications and their explanatory role

2 November 2026. These are source-verified examples from earlier work, not new experiments or newly proved application theorems. The files copied beside this index are unchanged public reports and proof sources. The current 36-obligation decomposition contract and the earlier operational/cylinder work must not be conflated.

## 1 Learning a predictable subsystem without identifying the whole environment

**Best main application.** `uncertain_coupling/Uncertain_coupling_mission_checkpoint.txt`, especially “A growing mission learned from local relations”; proof `uncertain_coupling/uncertain_coupling_mission_theorem.md`, Sections 2, 3 and 6.

An agent observes binary registers and a later load in an unfamiliar bounded-memory environment. It is not given the source grouping, overlap, exact delays or local equations. Safe local triple observations reveal that each next register equals the preceding register XOR a new input; endpoint probes reveal a useful delay at which the final register equals the load. The agent combines these learned relations to predict the later load from early values. Under the supplied interlock semantics, that prediction permits useful timely actuation.

This illustrates a useful discovered subsystem property: predictable behavior at the selected interface, despite uncertainty about the hidden realization. The learner does not need a complete causal model. Distinct physical filters can agree on every selected local probe and on this mission while disagreeing on a different joint question. Thus a description should state which future uses it supports, not advertise “the environment has been understood.”

The learning and mission theorem is conditional on stationary finite-memory binary-linear behavior, uniform independent innovations, known memory ceiling, reliable permitted probes, fresh blocks, safe isolation, supplied physical interlock and usable timing/resource envelopes. It does not discover those assumptions. Finite calibration has an explicitly charged failure allowance. The local probe scopes and the proposed mission interface have an exact algebraic coverage test; treating separate marginals as one joint experiment is invalid.

**Relationship to decomposition results.** This is an earlier operational application and cylinder-comparison integration, not an automatic corollary of every intrinsic graph-cut obligation. The final scientific review explicitly retained its conditional usefulness while crediting matched classical linear-algebra and verification baselines. Typed witnesses, interface preservation, joint constraints and controlled observational forgetting explain how such learned descriptions can be used and reorganized; they are not themselves an unrestricted discovery algorithm.

## 2 Reorganizing that learned subsystem without losing the useful guarantee

Sources: `crossing/Crossing_interfaces_and_mission_certificates.txt` and `crossing/crossing_certificate_transport.md`.

The same learned parity mission has two crossing ways to assign local work. In one arrangement each owner handles a source event and an update; its seam carries an intermediate parity. In the other, one owner supplies source values and another performs updates; its seam carries the input bits. Both actual controllers compute the same actuator output on every permitted input stream. Their communication needs differ, so agreement of output does not by itself preserve a deadline.

This gives a direct reason to care about changing a decomposition coherently: a discovered useful behavior may have to move between architectures or ownership boundaries. Retained event identities, evidence dependencies and resource premises say whether the guarantee survives that move. Removing the only timely bit route produces a conditional failure bound in the stated architecture. Retracting one learned relation invalidates the certificate; costed reacquisition can restore it only when the good physical regime still holds. Reacquiring evidence does not fix bad physics.

The report calls this a prospective RC4/RC7 bridge. It explicitly does not replace the intrinsic equipment, cut, incidence or I5 obligations. These crossing ownership charts are not falsely described as nested cuts in the original planar grammar.

## 3 Learning which operations form independent or contending subsystems

Sources: `anonymous_fifo/REPORT.txt`, Sections 1–4, and `anonymous_fifo/safe_anonymous_completion_theorem.md`; proofs in `queue_acquisition_draft.md` and `binding_certificate_draft.md`.

The learner can invoke addressed operations, but callbacks carry only timestamps, binary payloads and stream position. It does not know which operations share hidden FIFO servers. Solo and simultaneous pair probes yield service-duration bounds and reveal queue sharing when the timing bands separate. Individual callback origins need not be recovered to identify this partition.

The discovered operational semantics is directly useful: operations in a shared queue contend, while separate queues can proceed independently under the model. The learned partition and bounds support a production schedule. A joint matching certificate can determine the required role output even when some individual callback identities remain ambiguous. Full reconstruction would ask an unnecessarily strong question.

For a simple illustrative specialization of the supplied theorem, operations of duration 10 with report lag at most 1 can yield separate-queue completion by time 11, while learned lower bounds near 9 make a shared-queue pair finish no earlier than 18. A late anonymous pair completion distinguishes contention without labeling the two callbacks. This is a numerical explanation of the theorem, not a new measured system.

The trusted boundary includes fixed routing/durations, independent work-conserving nonpreemptive FIFO servers, known duration/lag bounds, reliable counts, safe and drained commissioning, and the independently supplied physical role/interlock relation. Timing does not discover the role meanings or certify these physical assumptions. This multiple-server model must not be silently merged with the separate single shared-priority example below.

## 4 Why one joint decomposition witness matters to the actual decision

Source already recovered under `stage_sources/return_cylinder_bridge_source/return_cylinder_bridge/return_cylinder_bridge_report.txt`, Sections 2–4 and 8.

Four jobs have roles A, B, A, B and learned priority comparisons 0 before 3 and 1 before 2. The observed report bits are 0011. Every one of the six globally compatible job orders requires role output 11. The controller can therefore certify that output without identifying the complete priority order.

If a summary retains only each job's separately possible ranks, it admits the impossible order (0,2,1,3), which violates 1 before 2 and would require 00. Every rank coordinate separately has a legitimate witness, but there is no single witness for the combination. The resulting relaxed model now refuses a command the exact joint model could certify. This is a loss of useful assurance through overapproximation, not an example of an unsafe approval.

Retaining the original precedence constraints or an equivalent full joint boundary relation repairs the loss without new sensing. The categorical cylinder construction represents those shared constraints and their coherent regrouping. Physical evidence generally only gives inclusion in that abstract relation; equality needs the report's additional full-record fixture assumptions. In particular, formal response predicates are not automatically executable sensors.

## Explanatory priorities

Lead with the decision and useful property, then introduce the mathematical distinction that makes the decision defensible. Use the learned-parity example to explain discovery of limited but useful semantics, crossing descriptions to explain reuse, and the priority example to explain why joint compatibility is operationally important. Use the graph topology audit as an additional structural application, not as a substitute for behavioral discovery. Do not claim a speed advantage, full hidden-mechanism recovery, or empirical safety certification.
