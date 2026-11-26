# Captured curves and recalibration

The pinned adapter transforms the node position but passes through world
trajectory control points. The separate [corridor result](Remaining_Curve_Clearance.tex)
checks a downstream consumer that explicitly retains a converted local curve.
Both endpoints can still be admissible after a correction while an unfinished
interior portion is not. Lean checks the scalar interval and clearance tests.

Use the parent [calibration replay pins](../README.md) (the original navigation
test is not used here). Also download these files from the same pinned tree
into the same directory under their original names:

- `vda5050_core/src/client/adapter/edge_request.cpp`
- `vda5050_core/include/vda5050_core/client/adapter/edge_request.hpp`
- `vda5050_core/include/vda5050_core/types/control_point.hpp`
- `vda5050_core/include/vda5050_core/types/trajectory.hpp`

Run with a C++20 compiler and Python 3:

```sh
python3 replay_native.py /path/to/pins > actual.txt
cmp native.txt actual.txt
python3 corridor.py actual.txt | cmp results.json -
```

`ResidualQuadratic.lean` checked in AXLE `lean-4.35.0` with Mathlib, three
axiom audits (propext, Classical.choice, Quot.sound only; no sorryAx).
This selected callback execution and authored model are not a controller
implementation, map activation test, or physical clearance result.

[Conditioning follow-up](pose-conditioned/): retain the shared offset between a bounded pose observation and the remaining curve, with exact drift sensitivity.
