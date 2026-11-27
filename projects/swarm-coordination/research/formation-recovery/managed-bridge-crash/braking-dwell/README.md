# Continuous link dwell before terminal rest

Does the link need to be acquired only after stopping? The exact scalar
model separates the opening of a continuous dwell from terminal rest.
All 36 re-runs on pinned warm KTH states found motions that keep clearance
and surviving links, begin the new geometric dwell under braking, and
finish at rest. The worst gap to the relaxed lower bound was 0.00101
model time units. This is not packet delivery or a local estimator.

[Proof, exact impossibility and matched service comparison](Braking_Dwell.tex).
Use [SOURCE.tsv](SOURCE.tsv) to supply the upstream files at their exact
relative paths, including the earlier study as `warm.py` in the input
directory. The runner needs Git, Python and NumPy.

    sh replay.sh /path/to/inputs | cmp expected.json -

`BrakingDwell.lean` checks the scalar inequality and rational witness
in Lean 4.35 with Mathlib, without `sorryAx`.
