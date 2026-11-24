# Corridor formation recovery after a crash

Can the surviving radio chain reconnect by a deadline while keeping continuous clearance from an immobile failed robot? [Statement, derivation and comparison](Corridor_Formation_Recovery.tex).

The exact test assumes known positions, fixed single-file order and endpoints, speed-bounded point motion, a known stationary body with no working radio, and distance-only links. Clearance holds throughout; connectivity is a terminal requirement unless it also holds initially. This is a physical feasibility oracle, not a local observation protocol or full R6 acceptance.

- `python3 replay.py | cmp replay.txt`: verifies 8,928 finite configurations against exhaustive enumeration.
- `OPENBLAS_NUM_THREADS=1 python3 lp_compare.py | cmp lp_compare.txt`: SciPy 1.17.0/HiGHS direct continuous LP comparison on 480 deterministic instances, with exact rational verification of proposed solutions.
- In a Lean 4.35.0 environment with Mathlib, run `lake env lean CorridorFormation.lean`. The AXLE replay checked `SwarmFormation.extend_exact`, `lastScan_exact`, `preserve_affine_gap`, and `interp_speed_normalized`, with no `sorryAx`. The written argument supplies the plant interpretation.
