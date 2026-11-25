# Exact recovery rates with overlapping pooled diagnostics

[Proof and certificates](Exact_Plans_From_Overlapping_Pools.tex). The result supplies a compact robust LP over local recovery probabilities even when several aggregate diagnostic pools overlap.

```sh
python3 -B replay.py | cmp - results.json
```

The runner uses SciPy/HiGHS for candidate plans and checks exact rational primal and dual certificates. It independently enumerates latent-law vertices on 108 small instances and validates four larger sparse-pool instances without vertex enumeration. `RiskCertificate.lean` checks the risk bound step in Lean 4.35.0 with Mathlib. This is a finite-law numerical design comparison, not a runtime or field-risk claim.

To verify the stored large-instance policies without SciPy, run `python3 -B verify_caps.py certificates.json`. The file carries feasible law witnesses and exact primal/dual rational certificates. Use the checker in ordinary Python mode (not `-O`). To regenerate both files: `python3 -B replay.py results.json certificates.json`.
