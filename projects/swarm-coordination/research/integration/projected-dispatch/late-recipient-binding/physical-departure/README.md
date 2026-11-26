# Physical departure qualifies a shared replacement recipient

[Source assumptions, proof and replay](Departure_Qualified_Binding.tex).
Actual pinned warehouse steps produce unload and exit times. An authored
bridge allows the shared destination only at the latter event, and pinned
radio dispatch tests the consequence. Direct exact scheduling ties.
The trace certificate depends on gate version, initial heading, timing,
and the qualified plant envelope through the duty. No deployment or
independent held-out test.

Materialize SOURCE.tsv, then run:

    sh replay.sh /path/to/upstream | cmp expected.json -

Requires Python 3.10+, NumPy, and C++17. Departure_Clock.lean contains
four checked projected-motion and integer-clock lemmas.

[Consume-cut alternative](../consume-cut/README.md) uses actual local receipt and active debit rows instead of predicting exact remote time. It distinguishes a stale read's non-delivering TX debit from withholding an attempt while other due work proceeds.
