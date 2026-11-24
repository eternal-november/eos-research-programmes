# Swarm coordination

How can groups keep doing joint work while communication, roles, and partners change and earlier commitments still bind?

The [research contract (v0.5)](contracts/Swarm_Coordination_Research_Contract_v0_5.tex) and [cascade acceptance protocol (v0.5)](contracts/Cascade_Acceptance_Protocol_v0_5.tex) are provisional.

Use Byzantine Control’s [fault inventory](../byzantine-control/FAULT-COVERAGE.md) to choose tests by mechanism, including stale information, pending work, and interacting timing changes. Check each mechanism against the swarm model before admitting it. The inventory is not an exhaustive list of swarm faults, and neither inventory selects or freezes contract tests.

Two provisional swarm inventories approach test selection from different directions: the [mechanism inventory](fault-inventory/Swarm_Coordination_Fault_Inventory.tex) maps faults to Byzantine Control’s categories; the [cleanroom inventory](fault-inventory/Swarm_Fault_Inventory_Cleanroom.tex) starts from service obligations and how to recognize a breach. Neither establishes fault tolerance or fixes the test cases.

Two existing negative controls help calibrate the tests: the [synthetic handoff comparison](../byzantine-control/portability/HANDOFF-RECEIPT-REUSE.md) shows a tie with a factored direct proof; the [B receiver regression](../byzantine-control/portability/B-RECEIPT-TICK.md) checks two timing changes that fail together at a supplied receiver state. Neither is a swarm result.

## Load-bearing handoff

**SC-LATCH: When can a crew release a load without missing another crew’s passage?** In the finite model, a partial latch and a missing report together make the incumbent’s unguarded release unsafe. A probe works when its readings distinguish the latch states and simultaneous support demands fit. [Model and timing argument](load-bearing-handoff/swarm-latch-pilot/Load_Bearing_Handoff_Pilot.tex) · [Pilot and replay instructions](load-bearing-handoff/swarm-latch-pilot/README.md). From the pilot directory: `python3 -B pilot.py --json | cmp results.json`.

**SC-LATCH-D: Which replacement support duties fit the same handoff?** With the handoff policy fixed, the selected quota-and-batch machine fits every declared world; the selected retry machine exceeds capacity when its retry overlaps the partial latch. Contextual matching and a factored direct check agree on the same joint worlds. [Transfer argument and selected findings](load-bearing-handoff/swarm-latch-transfer/Load_Bearing_Handoff_Transfer.tex) · [Frozen interface and replay](load-bearing-handoff/swarm-latch-transfer/INTERFACE.md). From the transfer directory: `python3 -B checker.py selected_positive.json` or `python3 -B checker.py selected_negative.json`.

These are conditional results for finite models. They neither validate a physical handoff nor pass v0.5’s cascade acceptance protocol.

## Connected handoff

**SC-CONNECTED: How far does the same request for relief have to travel?** Two reached cuts in the finite model give crew 0 the same request and deadline. A settled load lets the first receiving crew take over in one cut; a retained load requires a third crew in the other. An unrelated live load beyond the first free receiver stays untouched. With one-tick transfers and authorization sent only along the occupied chain, the earliest relief is the sum of the hop delays plus one tick per transfer. Factored matching and timing checks give the same answer. This is a calibration, not v0.5 cascade acceptance. [Model and proof](connected-handoff/Connected_Handoff_Locality_Pilot.tex) · [Replay instructions](connected-handoff/README.md) · [Checker](connected-handoff/pilot.py). From that directory: `python3 -B pilot.py --json | cmp results.json`.

## Distributed repair

**SC-TWO-BAY: When does a local hardware change require another crew to change its policy?** Two crews must deliver their held loads to different bays. Reversing one guide in both fixture modes leaves the other crew's feasible policy tables unchanged. Reversing it in only one mode forces a change to that crew's table, although either policy entry can stay unchanged in some repair. The exact joint relation detects the change; checking one entry at a time does not. The factored direct comparator gives the same result. [Model and proof](distributed-repair/two-bay/Distributed_Repair_Search_Pilot.tex) · [Checker](distributed-repair/two-bay/pilot.py).

**SC-FORK: When does a timely receipt make a fixed local policy possible?** In two reached cuts, one crew needs opposite actions under the same local view. A receipt before commitment separates the cuts; the same receipt after commitment does not. [Regression and proof](distributed-repair/fork-relief/Fork_Relief_Policy_Search.tex) · [Checker](distributed-repair/fork-relief/pilot.py).

From either study directory, run `python3 -B pilot.py --json | cmp results.json` to replay the saved checks. These are finite model results, not v0.5 cascade acceptance.
