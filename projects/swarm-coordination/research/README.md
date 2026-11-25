# Swarm coordination research

The [v0.5 completion review](COMPLETION.md) maps each written obligation to the corresponding proof and checks and states the limits of the results.

Use Byzantine Control’s [fault inventory](../../byzantine-control/FAULT-COVERAGE.md) to choose tests by mechanism, including stale information, pending work, and interacting timing changes. Check each mechanism against the swarm model before admitting it. The inventory is not an exhaustive list of swarm faults, and neither inventory selects or freezes contract tests.

Two existing negative controls help calibrate the tests: the [synthetic handoff comparison](../../byzantine-control/portability/HANDOFF-RECEIPT-REUSE.md) shows a tie with a factored direct proof; the [B receiver regression](../../byzantine-control/portability/B-RECEIPT-TICK.md) checks two timing changes that fail together at a supplied receiver state. Neither is a swarm result.

## Handoffs

### Load-bearing handoff

**SC-LATCH: When can a crew release a load without missing another crew’s passage?** In the finite model, a partial latch and a missing report together make the incumbent’s unguarded release unsafe. A probe works when its readings distinguish the latch states and simultaneous support demands fit. [Model and timing argument](handoffs/load-bearing-handoff/swarm-latch-pilot/Load_Bearing_Handoff_Pilot.tex) · [Pilot and replay instructions](handoffs/load-bearing-handoff/swarm-latch-pilot/README.md). From the pilot directory: `python3 -B pilot.py --json | cmp results.json`.

**SC-LATCH-D: Which replacement support duties fit the same handoff?** With the handoff policy fixed, the selected quota-and-batch machine fits every declared world; the selected retry machine exceeds capacity when its retry overlaps the partial latch. Contextual matching and a factored direct check agree on the same joint worlds. [Transfer argument and selected findings](handoffs/load-bearing-handoff/swarm-latch-transfer/Load_Bearing_Handoff_Transfer.tex) · [Frozen interface and replay](handoffs/load-bearing-handoff/swarm-latch-transfer/INTERFACE.md). From the transfer directory: `python3 -B checker.py selected_positive.json` or `python3 -B checker.py selected_negative.json`.

These are conditional results for finite models. They neither validate a physical handoff nor pass v0.5’s cascade acceptance protocol.

### Connected handoff

**SC-CONNECTED: How far does the same request for relief have to travel?** Two reached cuts in the finite model give crew 0 the same request and deadline. A settled load lets the first receiving crew take over in one cut; a retained load requires a third crew in the other. An unrelated live load beyond the first free receiver stays untouched. With one-tick transfers and authorization sent only along the occupied chain, the earliest relief is the sum of the hop delays plus one tick per transfer. Factored matching and timing checks give the same answer. This is a calibration, not v0.5 cascade acceptance. [Model and proof](handoffs/connected-handoff/Connected_Handoff_Locality_Pilot.tex) · [Replay instructions](handoffs/connected-handoff/README.md) · [Checker](handoffs/connected-handoff/pilot.py). From that directory: `python3 -B pilot.py --json | cmp results.json`.

### Timed support cascade

**SC-TIMED-SUPPORT: When do a delayed permit and a slower load transfer jointly miss a handoff deadline?** Either change alone fits. Both together free the middle support too late when an old load is live, but not after that load has settled. A permit sent before activation repairs the case when the order was already authorized. An independently selected bridge preserves the frozen receiver proof; opening it one tick later fails the authorization test. The modular direct proof matches the positive guarantee with fewer proof obligations. [Proofs and reproducible checks](handoffs/timed-support-cascade/README.md). This is finite receiver-level evidence, not full v0.5 acceptance.

**SC-RECOVERY-LANE: When does a required retry delay another handoff?** A failed inspection moves a retry onto the lane used by a live downstream transfer. The same two faults do not cascade when the retry uses a separate lane; that diagnostic adds capacity, while the installed earlier-permit repair does not. The [fault register](handoffs/timed-support-cascade/recovery-lane/FAULT_REGISTER.md), [review](handoffs/timed-support-cascade/recovery-lane/Integrated_Return_Review.tex), and [model](handoffs/timed-support-cascade/recovery-lane/Recovery_Lane_Cascade.tex) cover the two-workload return. Run `python3 -B verify_recovery.py` in the recovery-lane directory.

## Policy repair

**SC-TWO-BAY: When does a local hardware change require another crew to change its policy?** Two crews must deliver their held loads to different bays. Reversing one guide in both fixture modes leaves the other crew's feasible policy tables unchanged. Reversing it in only one mode forces a change to that crew's table, although either policy entry can stay unchanged in some repair. The exact joint relation detects the change; checking one entry at a time does not. The factored direct comparator gives the same result. [Model and proof](policy-repair/two-bay/Distributed_Repair_Search_Pilot.tex) · [Checker](policy-repair/two-bay/pilot.py).

[Lean proof and replay](policy-repair/two-bay/lean/README.md): `SwarmTwoBay.compatible_eq_iff`, `SwarmTwoBay.tailLayout_bijective`, and `SwarmTwoBay.normalized_tail_exact_codec` check the compatibility relation, its normal form, and the exact fixed-width membership codec. Run `./replay.sh /path/to/pinned/lake/project` from the proof directory.

**SC-FORK: When does a timely receipt make a fixed local policy possible?** In two reached cuts, one crew needs opposite actions under the same local view. A receipt before commitment separates the cuts; the same receipt after commitment does not. [Regression and proof](policy-repair/fork-relief/Fork_Relief_Policy_Search.tex) · [Checker](policy-repair/fork-relief/pilot.py).

From either study directory, run `python3 -B pilot.py --json | cmp results.json` to replay the saved checks. These are finite model results, not v0.5 cascade acceptance.

**SC-MODE-WINDOW-CERTIFICATE: When can a few histories refute every timed recovery option?** If each of the fixed recovery modes has one admissible start interval per history, two endpoint witnesses per mode suffice and are sometimes necessary. The same witness persists across replacement when its decisive endpoints tighten and its histories remain admitted. For several event times governed by difference bounds, each rejected mode has a short negative-cycle witness and an arc-by-arc proof reuse rule. [Proof](policy-repair/mode-window-certificates/Mode_Window_Certificates.tex) · [Lean, exact checks and index replay](policy-repair/mode-window-certificates/README.md).

**SC-SOURCE-QUALIFIED-ADMISSION: What does a healthy read actually protect through handoff?** An effector fence can postpone controlled withdrawal, not independent physical loss. The exact test keeps each source’s warning lead paired with its loss window; a warning branch must still provide productive fallback. [Proof](policy-repair/source-qualified-admission/Source_Qualified_Admission.tex) · [Lean and replay](policy-repair/source-qualified-admission/README.md).

**SC-DELAYED-ACCEPTANCE: Which part of a late receipt does a receiver need?** The exact one-receipt policy can combine a default start on silence with a separate start for each arrived observation. A physical acceptance timestamp can distinguish equal arrivals with disjoint start windows. If the sender must label before knowing delay, the minimum alphabet is a coloring of the start-window conflict graph; independent per-arrival labels can be too small. [Proof](policy-repair/delayed-acceptance/Delayed_Acceptance_Receipts.tex) · [Lean, actuator and direct-policy replay](policy-repair/delayed-acceptance/README.md).

## Joint risk

**SC-JOINT-RISK: Can two missing reports change joint risk without changing either local estimate?** Two admitted laws give the same probabilities for the observed report words and the same local health marginals. After two misses, the two-dispatch failure risks differ: (57611/149504) and (34661/149504). Both laws have the same ex-ante risk, (79/256). An observation preserves a product posterior exactly when its nonzero likelihood has rank one on the active product support. This is a finite model result, not a validated risk estimate or C6 acceptance. [Proof](joint-risk/degraded-reports/Joint_Risk_Under_Degraded_Reports.tex) · [Replay notes](joint-risk/degraded-reports/README.md) · [Checker](joint-risk/degraded-reports/pilot.py). From that directory: `python3 -B pilot.py --json | cmp results.json`.

**SC-SINGLE-RESERVE: When can one reserve protect two dispatches under degraded evidence?** The two mandatory dispatches use receivers that accept opposite support orientations. After two missed reports, the best worst-case risk with one reserve is 1/4, even with randomization. A timely shared bit comparing the orientations lets a single policy meet a 1/5 conditional risk bound under either model law at every reached report-and-bit history. With a truthful bit the worst conditional risk is 175/1024; the bound still holds with independent, calibrated bit errors up to 3427/84730. Direct minimax analysis gives the same result. This is a finite model guarantee, not a field result or C6 acceptance. [Proof](joint-risk/single-reserve/Risk_Intervention_With_Degraded_Reports.tex) · [Replay notes](joint-risk/single-reserve/README.md) · [Checker](joint-risk/single-reserve/pilot.py). From that directory: `python3 -B pilot.py --json | cmp results.json`.

**SC-RISK-REVISION: When does a revised risk cap bind work already admitted?** A later receipt can leave an expedited admission legal when it is made and still fail the revised cap if the exposure remains unresolved. Exempting an old commitment is a different rule. Timely relaxation recovers fast service on a reached cut; a tightening after an irrevocable reserve lock may be impossible to satisfy. [Proof](joint-risk/risk-cap-revision/Risk_Cap_Revision.tex) · [Replay](joint-risk/risk-cap-revision/README.md). This is an exact finite model, not a claim about field risk.

**SC-RECURRENT-RISK: When do repeated changes in evidence preserve a joint risk certificate?** Separate crew factors combine if the retained mode and survivor mass account for the joint dependence. A correlated censor can break the rule even when reported marginals match. Timely joint evidence can change the actual reserve choice. [Proof](joint-risk/recurrent-certificates/Recurrent_Risk_Certificates.tex) · [Replay](joint-risk/recurrent-certificates/README.md).

**SC-EXPOSURE-PROFILES: What history must survive a tighter cap on mission-wide risk?** A fixed latent defect mode couples prior and new exposure. Exact admission after a handoff reduces to membership in the old exposure set, with a sharp binomial bound on one-way summary states; contiguous itineraries permit a smaller exact code. The bound and cap-change law check in Lean. [Proof](joint-risk/exposure-profiles/Exposure_Profiles_And_Risk_Caps.tex) · [Replay and scope](joint-risk/exposure-profiles/README.md).

## Recurrent coordination

**SC-SETTLEMENT-FRONTIER: Which old receipts can a gate forget after rejoin?** For one fixed issuer with consecutive immutable IDs, the settled prefix and receipts above it reproduce exact admission; merging them agrees with union of learned facts. At the worst fixed counters, a reorder window of width B needs exactly B−1 more bits. Capping unresolved duties at three still allows 2n−2 distinguishable receipt states after n issues. A stalled first receipt can block issuance, and receipt merge does not reorder physical transfers. This is a finite protocol result, not a liveness theorem, full C2 acceptance, or an advantage over direct frontier tracking. [Proof](recurrent-coordination/settlement-frontiers/Settlement_Frontiers_Across_Rejoins.tex) · [Replay notes](recurrent-coordination/settlement-frontiers/README.md) · [Checker](recurrent-coordination/settlement-frontiers/pilot.py). From that directory: `python3 -B pilot.py --json | cmp results.json`.

**SC-TRANSFERABLE-SETTLEMENT: Can several issuers bound their combined settlement window when they rejoin?** In one non-forking history, the joined window fits the number of rights if publication carries settlement evidence for earlier uses of each right and for prior grants revealed by the issuer's sequence. Either missing dependency can exceed the bound. A missing first receipt can also block every right despite free supports. The matched proof with coalesced causal delivery gives the same result. [Proof](recurrent-coordination/transferable-settlement-rights/Transferable_Settlement_Rights.tex) · [Replay](recurrent-coordination/transferable-settlement-rights/README.md).

[Lean proof and replay](recurrent-coordination/transferable-settlement-rights/lean/README.md): `SwarmSettlement.all_views_right_unique_iff` checks the evidence criterion, and `SwarmSettlement.published_issuer_width_bound_of_no_holes` checks the normalized window bound. Run `bash replay.sh /path/to/pinned/lake/project` from the Lean directory. Certificate production and liveness are outside the proof.

**SC-STAGGERED-REJOIN: Can an old duty survive a split while crews disagree about membership?** A local interlock checks current pooled admissions while private work continues. Custody and physical settlement survive newer generations; stale requests cannot create duties. The stable-window bound is exact in terms of the enabling cuts of the declared model. [Proof](recurrent-coordination/staggered-rejoin/Staggered_Recognition_At_Rejoin.tex) · [Replay](recurrent-coordination/staggered-rejoin/README.md).

## Role changes

**SC-SPARE-SLOTS: When does a role handoff leave room for new work?** With authority held at an interlock and unit-length work using named worker-time slots, the exact admission profile records which slots can be spared together. Profiles combine across disjoint groups of old duties. Two matched histories with identical incoming authority and capacities disagree on a new admission because an earlier closure needs the relay's backup worker in only one history. A later public observation can invalidate the fixed-schedule model without invalidating a causal policy. The direct matching proof ties. [Proof](role-changes/spare-slots/Role_Changes_With_Pending_Work.tex) · [Replay notes](role-changes/spare-slots/README.md) · [Checker](role-changes/spare-slots/replay.py). From that directory: `python3 -B replay.py --verify | cmp results.json`.

**SC-GUARDED-ROLE: When must a promotion wait for a duty already owed?** Switching the gate and moving an old holder-bound ticket is one guarded action. An intact ticket can transfer; when it cannot, the previous bearer discharges it and the same promotion takes effect later. Relay and unrelated closures continue. [Proof](role-changes/guarded-transition/Guarded_Role_Transition.tex) · [Replay](role-changes/guarded-transition/README.md).

## Partner substitution

**SC-TIMELY-CLEARANCE: When can a replacement instrument preserve an installed service proof?** A partial sensor bank supplies the clearance certificate used by an unchanged receiver while older jobs hold physical reservations. Delivering the same certificate one tick later meets the standalone deadline but fails joint service. With any r lanes occupied, one service lane requires exactly r+1 distinguishable timely reports; two simultaneous lanes give a different exact bound. The factored direct proof reuses the same checks. [Proof](partner-substitution/timely-clearance/Certified_Lane_Substitution.tex) · [Replay notes](partner-substitution/timely-clearance/README.md) · [Checker](partner-substitution/timely-clearance/replay.py). From that directory: `python3 -B replay.py --verify | cmp results.json`.

**SC-SEPARATE-PROVIDERS: Can independently implemented sensors use the same receiving rule?** Full and restricted providers cross the same clearance boundary without reading one another's state. A late provider passes the standalone contract and fails the joint deadline. [Proof](partner-substitution/separate-providers/Separate_Clearance_Providers.tex) · [Replay](partner-substitution/separate-providers/README.md).

## Forecast preparation

**SC-FORECAST-CLEARANCE: When should a warning trigger preparation rather than avoidance?** The existing two-handoff scheduler determines whether an installation can use the spare slot without displacing old closures or relay coverage. With two matched forecast laws, optimized choices use both preparation and a separate detour below a sharp cost boundary for diversion. A late clearance loses the preparation option even on physically feasible runs; an independent gate can restore it by conditional authorization. A detour that competes with the relay is a distinct capacity failure. The factored direct proof ties. [Proof](forecast-preparation/inherited-work/Forecast_Preparation_With_Live_Duties.tex) · [Replay notes](forecast-preparation/inherited-work/README.md) · [Checker](forecast-preparation/inherited-work/replay.py). From that directory: `python3 -B replay.py --verify | cmp results.json`.

**SC-FORECAST-CONTROLS: When does preparation still pay with delayed or mistaken warnings?** Matched controls vary recipient, lead, errors, costs and reversal. Releasing a preparation can restore a route option, not its sunk slot or cost. [Proof](forecast-preparation/forecast-controls/Forecast_Control_Comparisons.tex) · [Replay](forecast-preparation/forecast-controls/README.md).

## Live synthesis

**SC-LIVE-DISPATCH: Can a verified policy be installed while earlier work continues?** Keeping one staging support free lets a compiler install a policy for a late fixture configuration and gain one tick of service. A catalogue of separate fixed images and a scalar replanner both have exact limitations under the declared interfaces; a general compiler ties. Holding the support costs one optional admission. [Argument](live-synthesis/dispatch-policy/Live_Latch_Policy_Synthesis.tex) · [Replay](live-synthesis/dispatch-policy/README.md).

## Goal revision

**SC-VESTED-LANE: Can a new goal restore a load to an apparently empty lane?** A still-binding right to start an old job can block restoration before it creates any occupation. The exact wait uses jointly admissible start and dwell, not separate scalar maxima. [Proof](goal-revision/vested-lane-use/Goal_Revision_With_Vested_Lane_Use.tex) · [Replay](goal-revision/vested-lane-use/README.md).

## Local perception

**SC-ANONYMOUS-BEARING: How much local history certifies safe entry without messages?** Two complete anonymous bearing frames distinguish safe entry in a finite two-peer crossing even with merged silhouettes. A frame clipped by the observation envelope can hide a decisive track. An explicit tracker and full direct temporal processing tie. [Proof](local-perception/anonymous-bearing/Anonymous_Bearing_and_Crossing.tex) · [Replay](local-perception/anonymous-bearing/README.md).

## Communication changes

[Communication and observation regimes](communication/Communication_Regimes.tex) is a working reference for choosing assumptions and comparison cases, including non-radio modalities and enclosed spaces. It is not an exhaustive inventory or a contract obligation.

**SC-MULTIMODAL-HANDOFF: When is a report usable for entry after communication changes?** Identity, direction and delivery time determine whether a clearance can shorten a handoff. In the absence of evidence, the bound uses the verified physical drain time, and identical current channel states can still have different waits. [Proof](communication/multimodal-bay/Multimodal_Bay_Handoff.tex) · [Replay](communication/multimodal-bay/README.md).

**SC-TWO-REPORT-OPTICS: How does an earlier delivery restrict the evidence a courier can acquire?** Known worlds finish by six ticks; one-way optical evidence supports an exact seven-tick local policy, while absent or possibly erased evidence requires eight. A mechanical latch can replace the pulse without rewriting the receiver only if its effect is earned before the read. [Statement and proof](communication/optical-rendezvous/Two_Report_Optical_Rendezvous.tex) · [Replay and scope](communication/optical-rendezvous/README.md).

## Active evidence

**SC-PROBE-COMPLEMENTARITY: When are two private probes worth buying together?** Each probe can fail to pay its own cost while both enable timely joint service. Earlier commitments restrict probe and bypass availability; a separate conservative reservation has an explicit opportunity cost. [Proof](active-evidence/probe-complementarity/Probe_Complementarity.tex) · [Replay](active-evidence/probe-complementarity/README.md).

**SC-COUPLED-RELAY-PROBE: Can an exit measurement consume capacity needed by an undelivered report?** With both reports already stored, a shorter route probe can identify the exit but disable the one relay still needed for delivery. A separately powered probe restores actual service. Learning that the far path is blocked can choose a different probe; the same-information direct route and matching planner ties. [Statement and proof](active-evidence/coupled-relay-probe/Coupled_Probe_And_Relay_Service.tex) · [Lean and replay](active-evidence/coupled-relay-probe/README.md).

**SC-INSPECTION-EVENT-ADAPTER: Which parts of the report and egress model survive variable action time?** The source adapter reads directed movement, physical intervals, costs, reports and shared slots from a fixture. It distinguishes actual payload arrival from receipt evidence. A restricted second crew can change an in-flight relay's physical support without sharing its private observations. [Statement](active-evidence/inspection-event-adapter/Mission_Event_Adapter.tex) · [Adapter, Lean and replay](active-evidence/inspection-event-adapter/README.md).

## Multiple owners

**SC-LANE-WITHDRAWAL: When can a successor start after an owner withdraws?** Port-side authority and physical clearance are different: a prior start can stay live after revocation. A receipt-only rule, a timeout and an independent reserve have different service consequences. [Proof](multi-owner-coordination/lane-withdrawal/Withdrawal_With_Live_Lane_Use.tex) · [Replay](multi-owner-coordination/lane-withdrawal/README.md).

**SC-SCOPED-ADVICE: Does a lawful expansion of permissions make the old report sufficient?** Exact admission under restricted disclosure retains only the currently authorized history predicates. A later grant can demand a distinction the old report deliberately omitted; the count of supplemental report states is exact. Lean checks the authorized profile and recovery obstruction. [Proof](multi-owner-coordination/scoped-advice/Scoped_Advice_And_Amendment.tex) · [Replay and scope](multi-owner-coordination/scoped-advice/README.md).

## Cross-group agreements

**SC-ORDERED-ACCESS: Can identical allocations allow different blocking coalitions?** Swapping the order of access rights can change a feasible coalition deviation without changing current jobs or payoff. Earliest feasible completion preserves the stated stability tests. [Proof](cross-group-agreements/ordered-access/Access_Windows_And_Blocking.tex) · [Replay](cross-group-agreements/ordered-access/README.md).

## Formation recovery

**SC-CORRIDOR-CRASH: Can a single-file radio chain reconnect after a dead robot blocks the lane?** For fixed order, known positions and speed-bounded motion, an exact interval scan decides safe recovery by a deadline. Clearance holds through the motion; initial loss of radio connectivity is allowed. Integer propagation and the real affine motion lemmas check in Lean; a continuous LP corroborates the deadline calculation. [Statement and proof](formation-recovery/corridor-crash/Corridor_Formation_Recovery.tex) · [Replay and scope](formation-recovery/corridor-crash/README.md).

**SC-CORRIDOR-CONTACT: Can the two sides reconnect without positions crossing the radio break?** With a known single-file obstacle and local side plans, independently choosing the closest safe endpoints is exact. With a hidden stopped position, a pair of otherwise feasible worlds defeats every shared left action; reliable contact or timeout restores feasibility at a tight deadline. [Statement and proof](formation-recovery/split-corridor/Split_Formation_Recovery.tex) · [Replay and scope](formation-recovery/split-corridor/README.md).

**SC-CORRIDOR-SERVICE: When does fault-tolerant connectivity deliver a report on time?** Independent split motion decides terminal connectivity with further radio losses but can miss a robust two-hop report deadline. A selected common relay block restores the exact deadline under the ordered geometry, and late loss separates radio reach from actual retained copies and available forwarding slots. [Proof](formation-recovery/resilient-corridor/Resilient_Corridor_Service.tex) · [Lean and replay](formation-recovery/resilient-corridor/README.md).
