# Inspection route evidence that consumes a shared radio slot

[Statement, proofs and model scope](Coupled_Probe_And_Relay_Service.tex).

- `python3 -B source.py | cmp replay.txt`: observation-only policy search,
  source effect replay, and nominal, single-condition and compound controls.
- `python3 -B factored.py | cmp factored.txt`: matched route and robust
  matching reference with both choices of probe/forward order.
- `python3 -B payload.py | cmp payload.txt`: exact minimal probe payload
  classes for two declared source families.
- `python3 -B mixed_access.py | cmp mixed-access.txt`: local access selects a different tester with a separately replayed comparator.
- `lake env lean ProbeSlots.lean`: three source-side role feasibility and
  obstruction lemmas in Lean 4.35.0 with Mathlib.

This is an authored mission calibration with a matched ordinary planner.
It is not the independently selected enclosed-space validation.
