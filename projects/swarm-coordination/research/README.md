# Swarm coordination research

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

## Policy repair

**SC-TWO-BAY: When does a local hardware change require another crew to change its policy?** Two crews must deliver their held loads to different bays. Reversing one guide in both fixture modes leaves the other crew's feasible policy tables unchanged. Reversing it in only one mode forces a change to that crew's table, although either policy entry can stay unchanged in some repair. The exact joint relation detects the change; checking one entry at a time does not. The factored direct comparator gives the same result. [Model and proof](policy-repair/two-bay/Distributed_Repair_Search_Pilot.tex) · [Checker](policy-repair/two-bay/pilot.py).

[Lean proof and replay](policy-repair/two-bay/lean/README.md): `SwarmTwoBay.compatible_eq_iff`, `SwarmTwoBay.tailLayout_bijective`, and `SwarmTwoBay.normalized_tail_exact_codec` check the compatibility relation, its normal form, and the exact fixed-width membership codec. Run `./replay.sh /path/to/pinned/lake/project` from the proof directory.

**SC-FORK: When does a timely receipt make a fixed local policy possible?** In two reached cuts, one crew needs opposite actions under the same local view. A receipt before commitment separates the cuts; the same receipt after commitment does not. [Regression and proof](policy-repair/fork-relief/Fork_Relief_Policy_Search.tex) · [Checker](policy-repair/fork-relief/pilot.py).

From either study directory, run `python3 -B pilot.py --json | cmp results.json` to replay the saved checks. These are finite model results, not v0.5 cascade acceptance.

## Joint risk

**SC-JOINT-RISK: Can two missing reports change joint risk without changing either local estimate?** Two admitted laws give the same probabilities for the observed report words and the same local health marginals. After two misses, the two-dispatch failure risks differ: (57611/149504) and (34661/149504). Both laws have the same ex-ante risk, (79/256). An observation preserves a product posterior exactly when its nonzero likelihood has rank one on the active product support. This is a finite model result, not a validated risk estimate or C6 acceptance. [Proof](joint-risk/degraded-reports/Joint_Risk_Under_Degraded_Reports.tex) · [Replay notes](joint-risk/degraded-reports/README.md) · [Checker](joint-risk/degraded-reports/pilot.py). From that directory: `python3 -B pilot.py --json | cmp results.json`.

**SC-SINGLE-RESERVE: When can one reserve protect two dispatches under degraded evidence?** The two mandatory dispatches use receivers that accept opposite support orientations. After two missed reports, the best worst-case risk with one reserve is 1/4, even with randomization. A timely shared bit comparing the orientations lets a single policy meet a 1/5 conditional risk bound under either model law at every reached report-and-bit history. With a truthful bit the worst conditional risk is 175/1024; the bound still holds with independent, calibrated bit errors up to 3427/84730. Direct minimax analysis gives the same result. This is a finite model guarantee, not a field result or C6 acceptance. [Proof](joint-risk/single-reserve/Risk_Intervention_With_Degraded_Reports.tex) · [Replay notes](joint-risk/single-reserve/README.md) · [Checker](joint-risk/single-reserve/pilot.py). From that directory: `python3 -B pilot.py --json | cmp results.json`.

## Recurrent coordination

**SC-SETTLEMENT-FRONTIER: Which old receipts can a gate forget after rejoin?** For one fixed issuer with consecutive immutable IDs, the settled prefix and receipts above it reproduce exact admission; merging them agrees with union of learned facts. At the worst fixed counters, a reorder window of width B needs exactly B−1 more bits. Capping unresolved duties at three still allows 2n−2 distinguishable receipt states after n issues. A stalled first receipt can block issuance, and receipt merge does not reorder physical transfers. This is a finite protocol result, not a liveness theorem, full C2 acceptance, or an advantage over direct frontier tracking. [Proof](recurrent-coordination/settlement-frontiers/Settlement_Frontiers_Across_Rejoins.tex) · [Replay notes](recurrent-coordination/settlement-frontiers/README.md) · [Checker](recurrent-coordination/settlement-frontiers/pilot.py). From that directory: `python3 -B pilot.py --json | cmp results.json`.

## Role changes

**SC-SPARE-SLOTS: When does a role handoff leave room for new work?** With authority held at an interlock and unit-length work using named worker-time slots, the exact admission profile records which slots can be spared together. Profiles combine across disjoint groups of old duties. Two matched histories with identical incoming authority and capacities disagree on a new admission because an earlier closure needs the relay's backup worker in only one history. A later public observation can invalidate the fixed-schedule model without invalidating a causal policy. The direct matching proof ties. [Proof](role-changes/spare-slots/Role_Changes_With_Pending_Work.tex) · [Replay notes](role-changes/spare-slots/README.md) · [Checker](role-changes/spare-slots/replay.py). From that directory: `python3 -B replay.py --verify | cmp results.json`.

## Partner substitution

**SC-TIMELY-CLEARANCE: When can a replacement instrument preserve an installed service proof?** A partial sensor bank supplies the clearance certificate used by an unchanged receiver while older jobs hold physical reservations. Delivering the same certificate one tick later meets the standalone deadline but fails joint service. With any r lanes occupied, one service lane requires exactly r+1 distinguishable timely reports; two simultaneous lanes give a different exact bound. The factored direct proof reuses the same checks. [Proof](partner-substitution/timely-clearance/Certified_Lane_Substitution.tex) · [Replay notes](partner-substitution/timely-clearance/README.md) · [Checker](partner-substitution/timely-clearance/replay.py). From that directory: `python3 -B replay.py --verify | cmp results.json`.

## Forecast preparation

**SC-FORECAST-CLEARANCE: When should a warning trigger preparation rather than avoidance?** The existing two-handoff scheduler determines whether an installation can use the spare slot without displacing old closures or relay coverage. With two matched forecast laws, optimized choices use both preparation and a separate detour below a sharp cost boundary for diversion. A late clearance loses the preparation option even on physically feasible runs; an independent gate can restore it by conditional authorization. A detour that competes with the relay is a distinct capacity failure. The factored direct proof ties. [Proof](forecast-preparation/inherited-work/Forecast_Preparation_With_Live_Duties.tex) · [Replay notes](forecast-preparation/inherited-work/README.md) · [Checker](forecast-preparation/inherited-work/replay.py). From that directory: `python3 -B replay.py --verify | cmp results.json`.
