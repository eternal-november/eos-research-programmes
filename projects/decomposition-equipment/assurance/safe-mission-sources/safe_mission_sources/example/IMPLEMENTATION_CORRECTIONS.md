# Implementation corrections, not experiment retuning

The original experiment manifest was frozen before outcome runs. Independent
review found that the first runner version represented six-tick bay transfers by
phase labels, without a location state or a movement model. The corrected runner
uses an explicit legal bay chain (calibration -> aggregate -> individual ->
mission), enforces sensor/command availability by that state, and integrates each
one-metre transfer using the same coarse physical envelope as slow delivery.
Each transfer therefore takes ten quarter-second ticks. This is a correction of
an unsupported transfer claim, not a tuned experimental advantage. Added sensor
acquisition ticks are also charged. All original sizes, seeds, truth-family,
mission orders, speed contracts and deadline rules are unchanged.

Abstract energy is now explicitly recorded as one base unit plus one per active
command port per tick. A mission budget of three units per allowed tick is
nonbinding under the two-command mission cap; no discovery advantage from a
binding energy constraint is claimed, and these are not measured joules.

The initial singleton acquisition transcript is generated in the constructed
OR/XOR family. Continuation certificates quantify every persistent world
consistent with that realized transcript. The broad initial learner universe
also contains all-low mechanisms, so unconditional completion from every member
of that universe is false. A failure to recover a usable interface must cause
refusal, not an unsupported completion claim. The current constructed experiment
uses assertions to check the advertised generated family, not as a general
runtime handling policy outside it.

This growing family is a transparent integration demonstrator. Its residual
one-bit-per-response tree problem is ordinary parity-like constraint solving.
It is not the sole evidence for the harder partial-knowledge mission target.

A second review identified that adding actual commissioning duration to the
first service deadline was a two-phase measured allowance rather than a fixed
pre-run end-to-end budget. The earlier result is preserved in
`constructed_results_before_fixed_cap.json`. The corrected public acquisition
cap, computed before the recheck, is

  1 + n*(L+1) + 3*10 + edge_count*(L+1) + L+1 ticks.

It charges initial flush, every singleton probe/flush, three ten-tick coarse
transfers, worst-case preparation plus sampling per aggregate, and individual
preparation/sampling. It depends only on public dimensions/protocol, not outcomes.
The first mission's fixed deadline is this cap plus 60 ticks per delivery; actual
commissioning cost is still reported separately. Baselines receive this SAME
fixed total allowance. This repair permits the coarse baseline's first mission
in both the smallest and next-smallest cases; it is not hidden.
