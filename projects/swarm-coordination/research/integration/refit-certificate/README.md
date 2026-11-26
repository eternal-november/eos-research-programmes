# Clearance after a fitted evidence law changes

Exact least-squares fixture with full-rank authored calibration points.
A convex-hull capsule is sufficient for later affine clearance checks;
old separate extrema and the old active-model minimum need not be.
No sensor calibration or physical safety is claimed.

`Refit_And_Certificates.tex` states the exact boundary for min-score
queries over a convex-hull capsule. `Cert.lean` checks the affine kernel,
finite fixture, and insertion inequality. Execute `python3 -B replay.py
| cmp results.txt -` from this directory. Run Lean 4.35.0 with Mathlib.
