# Can the deciding robot obtain the cave gate cue?

[Technical note](A_Gate_Within_Range_Can_Still_Be_Unobserved.tex).
This source preflight checks an idealized scan lattice and sampling
budget, not actual rendered geometry, hardware or full sensor fusion.
The two compared scanner layouts are configuration controls, not a
matched-resource advantage.

Put the published source files named in `SOURCE.tsv` beside the replay
under the names in column 1. It checks original Git blob IDs. Run:

    node replay.mjs | cmp - expected.json

The timing lemmas in `TimelyScan.lean` were checked by AXLE with
Lean 4.36.0 and Mathlib.
