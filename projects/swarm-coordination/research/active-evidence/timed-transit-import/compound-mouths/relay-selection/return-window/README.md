# Return to contact before relay selection

[Technical note](Return_Window.tex). Held-in calibration on the published
Cave Circuit 01 graph under the parent experiment's selected hard RF gates.
Two independent motion enumerations and a finite local-policy check.
No physical motion, native packet, active sensor, or acceptance result.

Put the two original files in `SOURCE.tsv` beside the replay under the
names in column 1. Run `node replay.mjs | cmp - expected.json`.
The script checks each original Git blob. The three causal-table lemmas
in `ReturnWindow.lean` passed Lean 4.36.0 and Mathlib via AXLE.

[Sensor preflight for the gate cue](lidar-cue/README.md): a published range limit and scan rate do not establish that the deciding robot can classify the gate in time.
