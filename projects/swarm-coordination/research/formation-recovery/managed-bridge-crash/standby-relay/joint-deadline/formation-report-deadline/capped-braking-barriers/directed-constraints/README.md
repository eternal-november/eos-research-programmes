# Braking under directed relative-position constraints

The exact controlled invariant set uses the shortest-path position bound for every reachable pair, not just the original edges. The result applies to mixed velocity orders and common acceleration and braking limits, even when those two limits differ. Different bounds across robots admit a three-robot counterexample.

[Continuous proof](Directed_Braking_Kernel.tex) · [Lean arithmetic](DirectedOverlap.lean) · [Rational replay](replay.py) · [Recorded checks](results.json)

Run python3 replay.py and compare stdout with results.json. This model assumes full initial state and no new fault before rest.
