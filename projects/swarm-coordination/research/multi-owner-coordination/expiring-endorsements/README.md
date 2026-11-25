# Expiring endorsements and live holds

[Statement and proof](Expiring_Endorsements_And_Live_Holds.tex). Two ledgers can agree after every single recognized endorsement window and disagree after two successive windows. The general result gives the exact integer mass needed to hide a specified interaction and a decoder for wider interactions when the mass is too small.

```sh
python3 -B replay.py | cmp - results.json
```

The replay uses only the Python standard library. It compares direct ledger execution and exact summaries, tests the signed witnesses, checks the finite-mass decoder, and checks continuation after a consumed window. [Lean](Endorsements.lean) checks the primitive continuation law, down-closure invariance and sharp two-window mass result with Lean 4.35.0 and Mathlib. The general-width theorem is proved in the note, not claimed formally verified.

This is a model of a specified effect gate. It does not permit pooling expired approvals or cover deployments in which recognition and release are separated by an unmodeled interval.
