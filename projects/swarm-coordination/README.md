# Swarm coordination

How can groups keep doing joint work while communication, roles, and partners change and earlier commitments still bind?

The [research contract (v0.5)](contracts/Swarm_Coordination_Research_Contract_v0_5.tex) and [cascade acceptance protocol (v0.5)](contracts/Cascade_Acceptance_Protocol_v0_5.tex) are provisional.

Use Byzantine Control’s [fault inventory](../byzantine-control/FAULT-COVERAGE.md) to choose tests by mechanism, including stale information, pending work, and interacting timing changes. Check each mechanism against the swarm model before admitting it. The inventory is not an exhaustive list of swarm faults, and no cases have been selected or frozen here.

Two provisional swarm inventories approach test selection from different directions: the [mechanism inventory](fault-inventory/Swarm_Coordination_Fault_Inventory.tex) maps faults to Byzantine Control’s categories; the [cleanroom inventory](fault-inventory/Swarm_Fault_Inventory_Cleanroom.tex) starts from service obligations and how to recognize a breach. Neither establishes fault tolerance or fixes the test cases.

Two existing negative controls help calibrate the tests: the [synthetic handoff comparison](../byzantine-control/portability/HANDOFF-RECEIPT-REUSE.md) shows a tie with a factored direct proof; the [B receiver regression](../byzantine-control/portability/B-RECEIPT-TICK.md) checks two timing changes that fail together at a supplied receiver state. Neither is a swarm result.
