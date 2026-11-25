# Two repairs sharing a live fixture

[Model, release law, and delayed-authority theorem](Shared_Fixture_Release.tex)
· [Lean arithmetic](ActualRelease.lean).

```sh
set -o pipefail
python -B replay.py | cmp result.txt -
lean ActualRelease.lean
```

The independent Python model enumerates mount, hold and actual transfer
events, with one common history before the permission readout. It checks
864 timing tuples, including 199 where advance information changes the
best guarantee. A separate exhaustive permutation comparison checks the
known-permission order rule on 1,024 selected parameter sets. Lean 4.35.0
and Mathlib check two arithmetic lemmas, not plant behavior.
