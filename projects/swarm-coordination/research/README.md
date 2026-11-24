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

## Policy repair

**SC-TWO-BAY: When does a local hardware change require another crew to change its policy?** Two crews must deliver their held loads to different bays. Reversing one guide in both fixture modes leaves the other crew's feasible policy tables unchanged. Reversing it in only one mode forces a change to that crew's table, although either policy entry can stay unchanged in some repair. The exact joint relation detects the change; checking one entry at a time does not. The factored direct comparator gives the same result. [Model and proof](policy-repair/two-bay/Distributed_Repair_Search_Pilot.tex) · [Checker](policy-repair/two-bay/pilot.py).

**SC-FORK: When does a timely receipt make a fixed local policy possible?** In two reached cuts, one crew needs opposite actions under the same local view. A receipt before commitment separates the cuts; the same receipt after commitment does not. [Regression and proof](policy-repair/fork-relief/Fork_Relief_Policy_Search.tex) · [Checker](policy-repair/fork-relief/pilot.py).

From either study directory, run `python3 -B pilot.py --json | cmp results.json` to replay the saved checks. These are finite model results, not v0.5 cascade acceptance.
