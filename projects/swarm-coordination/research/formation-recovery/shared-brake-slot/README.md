# Shared-brake formation tube

An equal split can keep an exact gap while an exclusive fixed-slot brake
must spend clearance or communication slack. The project gives a sharp
tube test, a parity obstruction at the stop, and a faster-hold repair for
the same physical deadline. The direct exhaustive comparison agrees.

[Proof, parameters and comparisons](Shared_Brake_Tube.tex) · [Lean](Brake.lean).

    python3 -B replay.py | cmp expected.json -

Modeled continuous trajectories with a fixed command grammar, not a
vehicle or packet-reliability test. Python standard library only.
