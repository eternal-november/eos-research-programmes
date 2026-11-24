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
