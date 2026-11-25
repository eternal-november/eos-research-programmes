# Reserve staging and shared supplier recovery

[Model and proofs](Reserve_Staging_Certificates.tex). An exact robust placement test and a sharp bound on how many fault cases are needed to rule out each permitted location. This is a single-loss, one-spare boundary for R2/L3, not an independent transfer or architecture acceptance.

```sh
python3 -B replay.py | cmp - results.json
```

Lean 4.35.0 with Mathlib checks the abstract certificate lemmas in `Staging.lean`. The physical transition search is a civil simulation, with no external dependencies.
