# Radio margin and obstacle reports

Continuation of the [relay-lens model](../relay-lens). Exact asymmetric link-range threshold and worst-world arrival with a single obstacle-side report. The continuous argument compares all speed-only causal paths in this model; no real RF, platform energy, or actuator guarantee is inferred.

- [Proof and numerical example](Radio_Margin_And_Obstacle_Reports.tex)
- [Lean arithmetic kernels](AsymmetricRelayLens.lean) (Lean 4.35.0 + Mathlib)
- Replay: run `python replay.py` with SciPy and compare with `replay.txt`. The true-arc graphs are bounded numerical competitors, not the continuous lower-bound proof.
