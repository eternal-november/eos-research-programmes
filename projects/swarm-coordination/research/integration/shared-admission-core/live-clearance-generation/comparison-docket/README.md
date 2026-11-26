# I1 comparison and pre-freeze docket

[Source scope, audited results, and next discriminator](I1_Comparison_Docket.tex).
This is a held-in docket, not an acceptance report or an evaluation freeze.
The checker verifies seven fixed replay results and an exact synthetic
adaptive acquisition example against an independent possible-world search.

Materialize the pinned JSON files in `SOURCE.tsv` and run using Python 3.10+
and a shell with pipefail:

    python3 -B check.py /path/to/materialized-results | cmp expected.json -

This command audits pinned replay outputs; it does not rebuild their native
simulators. Each of the original replays documents its own rebuild.
