# Source-step lease across asynchronous consumption

[Scope and proof](Earliest_Return_Lease.tex). The source proves no return
before a counted number of its own actions; the broker still checks its
native budgets locally at effect. The timing envelope tying these clocks
together is supplied by the fixture.

Materialize the inputs in `SOURCE.tsv` and run with Python 3.10+, NumPy and
C++17, using a shell with pipefail:

    sh replay.sh /path/to/materialized-sources | cmp expected.json -

The replay checks the exact blob hashes. `Elapsed_Steps.lean` checks the
time-envelope calculation in Lean 4.35.0 with Mathlib.
