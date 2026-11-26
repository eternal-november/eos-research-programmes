# Native recurring request and application-key closure

[Scope, witnesses and proof](Recurring_Request_Closure.tex). A pinned
RWARE replay cycles a genuine request from A to B to A. At restart,
even exact current warehouse observations augmented with the entire
request queue can be insufficient to decide whether the original
application request already received station credit.

Materialize the sources pinned in `SOURCE.tsv`, then run with Python 3.10+
and NumPy, using a shell with pipefail:

    sh replay.sh /path/to/materialized-sources | cmp expected.json -

`Keyed_Closure.lean` checks the identical-view result and key separation
in Lean 4.35.0 with Mathlib.
