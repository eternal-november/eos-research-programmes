# Certificates for timed recovery alternatives

[Statement, proof and limits](Mode_Window_Certificates.tex). A receiver facing alternative physical modes can reject a whole information class with two endpoint witnesses per mode. The bound is tight, and pairwise joint compatibility alone can give a false pass.

- `python3 replay.py | cmp replay.txt`: exact diagnostic and tight families.
- `python3 indexed.py | cmp indexed.txt`: benchmark for known endpoint changes against full enumeration.
- `lake env lean ModeWindowCertificates.lean` in Lean 4.35.0 with Mathlib. Seven exported statements checked, no `sorryAx`.

Reusing rejection requires the source histories to remain admissible and their decisive endpoints to be unchanged or tighter. New physical options, missing source evidence, and the expense of discovering edits are outside the heap guarantee.
