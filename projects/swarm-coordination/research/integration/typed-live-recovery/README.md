# Typed live recovery under a second fault

[Statement, physical adapters, and scope](Physical_Staging_And_Typed_Live_Recovery.tex).

Run `python3 -B integration.py | cmp replay.txt` and `python3 -B reserve.py | cmp reserve.txt`. Lean 4.35.0 with Mathlib checks the four lemmas in `StagedCommit.lean`. These are development cases. They do not establish an independent transfer, an advantage over the strongest matched method, or I1 coverage.
