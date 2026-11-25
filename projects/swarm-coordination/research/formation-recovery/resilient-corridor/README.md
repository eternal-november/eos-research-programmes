# Robust connectivity and timed radio service in a single-file corridor

[Statement and proofs](Resilient_Corridor_Service.tex).

- `python3 -B replay.py | cmp replay.txt`: exact physical placements, radio deletion and cross-link witnesses.
- `python3 -B deadline.py | cmp deadline.txt`: independent deletion and shortest-path comparisons.
- `python3 -B service.py | cmp service.txt`: two-hop service placement and a counterexample to reusing cut-directed extrema.
- `python3 -B evidence.py | cmp evidence.txt`: same-cut anchor evidence and stale split views.
- `python3 -B effect.py | cmp effect.txt`: actual copies and forwarding slots under later radio loss.
- `lake env lean ResilientCorridor.lean`: five supporting lemmas checked in Lean 4.35.0 with Mathlib.

The two-hop placement rule uses a common selected relay block. The earlier
independent extrema only decide robustness of connectivity, not its hop
deadline. Experiments are finite model checks, not hardware trials.
