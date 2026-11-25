# A reversible load test for support readiness

[Statement and proof](Active_Support_Probe.tex). Run `python3 -B check.py | diff - replay.txt`.

Two replacement configurations agree at rest. A local mechanical test resolves them only when its differential response beats bias drift and measurement error while leaving time to restore the probe. A direct active estimator with the same resources ties. The test authorizes choosing a replacement, not releasing the old support before actual transfer. No validated calibration, field claim, independent holdout, or R1 acceptance.
