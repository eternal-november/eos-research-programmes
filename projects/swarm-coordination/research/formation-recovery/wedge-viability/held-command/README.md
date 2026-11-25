# Held-command wedge braking

The exact continuous wedge result assumes a controller can change acceleration when needed. This study finds the longest safe first command on a symmetric tight family and, at slope two, gives an exact fixed update period and a constructive retreat. A hold can pass its entire segment's collision test and nonetheless end with no safe continuation.

Run `python -B check.py` and compare with `replay.txt`. The separate TeX proof covers continuous trajectories and states exactly where the fixed-period result stops.

Three algebra checks, including a safe held endpoint with no viable continuation, are in `HeldWedgeAlgebra.lean` and were checked with Lean 4.35.0 and Mathlib. The dynamic proofs are analytic.
