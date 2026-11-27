# An acceleration limit moves the latest useful notice earlier

[Proof and witness](Acceleration_Notice_Cut.tex). For the modeled peak
6.37, both inspection windows are still physically feasible under
unit speed and acceleration bound 10. But the latest truthful
notice is about 0.604725 rather than the position-only 0.648333.
At the sharp cutoff, the shared pre-notice maneuver prepares velocity
for the far window while leaving just enough braking to meet the
late window's seam.

Run `node replay.mjs | cmp expected.json -` with Node 22 or later.
The replay ran in V8 without a shell. It checks 1,950 exact endpoint
momentum-bound comparisons and 53 notice cuts, including a rational
isolation of the sharp cutoff. The accepted paths are checked at
quadratic extrema, not just on time samples. Lean 4.36.0 and Mathlib
check the scalar inequality kernel. No jerk constraint, measured
mobility or working notice channel is implied.
