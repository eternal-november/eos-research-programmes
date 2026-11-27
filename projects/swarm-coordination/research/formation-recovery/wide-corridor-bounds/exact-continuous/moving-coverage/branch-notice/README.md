# A late inspection notice can arrive after the last useful motion

[Proof and model](Branch_Notice_Cut.tex). The mobile robot may start
moving before it knows which inspection window is owed, but that motion
must preserve both continuations. At a far-window peak of 5.5, the exact
notice cutoff is 1.5 time units. At a peak of 6.37, the cutoff is 389/600:
later than waiting to move until notice, but still before the start of
the other window's mandatory seam overlap. At 6.38, even knowing the
window immediately cannot help.

The integer-rational JavaScript replay matches an independent
difference-constraint solver and checks both reconstructed trajectories
for continuous coverage. It ran in V8 without a shell or renderer.
Run `node replay.mjs | cmp expected.json -` with Node 22 or later for
a local replay. Lean 4.36.0 and Mathlib check three arithmetic and
propagation lemmas. No actual sensor, fault-report infrastructure,
new speed guarantee over the same-information planner, or independent
mission is claimed.

[Acceleration-limited notice cutoff](bounded-acceleration/README.md)
shows the position-only cutoff is too late even when both known worlds
remain physically feasible. The exact worked example retains velocity.
