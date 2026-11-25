# Certificates for timed recovery alternatives

[Statement, proof and limits](Mode_Window_Certificates.tex). A receiver facing alternative physical modes can reject a whole information class with two endpoint witnesses per mode. The bound is tight, and pairwise joint compatibility alone can give a false pass.

- `python3 replay.py | cmp replay.txt`: exact diagnostic and tight families.
- `python3 indexed.py | cmp indexed.txt`: benchmark for known endpoint changes against full enumeration.
- `lake env lean ModeWindowCertificates.lean` in Lean 4.35.0 with Mathlib. Seven exported statements checked, no `sorryAx`.

Reusing rejection requires the source histories to remain admissible and their decisive endpoints to be unchanged or tighter. New physical options, missing source evidence, and the expense of discovering edits are outside the heap guarantee.

## Several coupled event times

[Difference-bound extension and source case](Timed_Event_Certificates.tex). `python3 vector_replay.py | cmp vector_replay.txt` checks 2,400 exact matches, the tight witness family, and the [frozen flag-source example](../../communication/optical-rendezvous/README.md). `lake env lean TimedEventCertificates.lean` checks the negative-cycle and replacement kernels without `sorryAx`. The interval replay remains the single-time specialization.
