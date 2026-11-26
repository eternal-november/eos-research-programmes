# Shared calibration and timed occupancy

[Joint cut proof](Joint_Clock_And_Calibration_Cut.tex).
The time-only and geometry-only peak can both be two when the exact combined
peak is one. Geometry can require checking triples even when every pair is
compatible. The method produces a joint witness and reuses old footprint
intersections when only the support for the common translation changes.

From this folder, with the parent temporal occupancy replay available:

```sh
python3 replay.py | cmp results.json -
```

The model reuses the parent's positive half-open integer STN semantics.
The closed site footprint, shared planar translation and independence of the
timing constraints within each declared branch are new pins. The companion
[VDA callback replay](../../../../released-base-cut/calibration-capture/) checks
why captured local targets matter, not whether the new physical assumptions
hold. No field or architecture acceptance is claimed.
