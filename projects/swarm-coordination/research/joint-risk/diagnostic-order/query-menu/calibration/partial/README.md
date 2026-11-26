# Partial calibration with adaptive measurement

[Proof and thresholds](Partial_Calibration_And_Adaptive_Choice.tex) · [model freeze](FREEZE.txt).
Reading at most one candidate bundle per episode costs a factor equal to
the number of candidate bundles in the stated family, even with adaptive
measurement. The sufficient contrast does not need the window flag or
its exact prevalence.

    python3 -B replay.py | cmp results.json -

The checker uses Python 3.10+ and exact rational probabilities. It includes
a small same-information adaptive allocation oracle. The sample bounds
are for a stated observation model, not a measurement or a safety certificate.
