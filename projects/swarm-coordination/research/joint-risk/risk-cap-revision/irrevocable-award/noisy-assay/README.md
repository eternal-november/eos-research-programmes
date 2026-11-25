# Value of a noisy assay before a second award

[Proof](When_The_Assay_Pays.tex) · [Scope freeze](FREEZE.txt). The calibration error and the work forfeited to get the evidence jointly determine whether an assay helps. At the quarter-unit cost, the exact symmetric flip cutoff is 1/6.

From this directory in the repo, run:

```sh
python3 -B replay_noisy.py ../replay.py | cmp - results.json
```

The matching raw comparison uses the parent exact rational certificate code with SciPy/HiGHS candidates. `AuditThreshold.lean` checks both inequality thresholds in Lean 4.35.0 with Mathlib. The Space archive also carries the exact parent Python input. The finite models are authored, not physical calibration.
