# Exact wedge braking with late lateral evidence

The continuous-time proof gives the exact viability kernel for Breeden and Panagou's wedge with slopes at least one, and a counterfamily below that slope. It also computes the extra starting clearance required when the lateral velocity's sign cannot be observed until after braking has started. This does not model a full formation or prove mission completion.

Run `python -B check.py` to replay the rational tests and compare with `replay.txt`. The three algebra lemmas were checked with Lean 4.35.0 and Mathlib; the analytic tangent-cone proof is in the TeX note.
