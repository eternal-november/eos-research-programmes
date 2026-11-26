# Reuse an axis, not a stale motion command

[Model, pulse derivation, and results](Uncertain_Cut.tex). An
earlier fault in the same branch of the warm planar example may
barely change position but leave enough velocity to invalidate the
old acceleration profile. A timestamp-conditioned two-pulse motion
reuses the nominal axis in checked cases the brake-first procedure misses.

Materialize the inputs in `SOURCE.tsv`; Python 3.10+, NumPy and SciPy:

    set -o pipefail
    sh replay.sh /path/to/materialized-sources | cmp expected.json -

`Two_Pulse.lean` checks the switched endpoint identity and residual
velocity arithmetic on Lean 4.35.0 with Mathlib.
This is not a uniform interval, actual cutoff sensor, or
published crash-controller replication.
