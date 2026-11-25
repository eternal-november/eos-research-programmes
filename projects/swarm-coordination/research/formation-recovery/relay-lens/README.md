# Relay crossing with two continuous radio links

[Geometry and causal deadline proof](Relay_Lens_And_Late_Sign.tex) · [Lean kernels](RadioLens.lean)

```sh
set -o pipefail
python3 -B lens_probe.py | cmp lens.txt -
python3 -B hidden_probe.py | cmp hidden.txt -
python3 -B geodesic.py | cmp geodesic.txt -
python3 -B limits.py | cmp limits.txt -
lean RadioLens.lean
```

The numeric references use SciPy 1.17.0. Lean 4.35.0 with Mathlib checks eight algebraic statements. The exact deadline theorem is for the speed-limited civil model with a single trustworthy sign disclosure at a specified time, not for a measured radio network. The constant-speed acceleration comparison is separate.
