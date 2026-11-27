# Committed read dependencies across two station handoffs

[Technical note](Committed_Dependencies.tex). In the pinned RWARE wrapper,
a pending retry reads the native ordered log, but a completed retry
with the right keyed result reads only the authority, permit and receipt.
When a second request commits, the first request's completed read record
can stay valid at the same station while the second request changes
from pending to cached. After transfer, a different publisher identity
requires a fresh authority check even if the underlying result is the same.

The 24 joined histories run two real SQLite publication fences and two
native restartable steps, plus an independent carrier during the waiting arm.
A same-information direct implementation matches service and uses fewer
copy bytes in this fixture. A copied seal by itself can authorize two
writable destinations, so exclusive destination selection is a premise.
This is not a distributed handoff authority, a field qualification,
an independent mission, or R2/I1 acceptance.

Materialize the exact station wrapper from `STATION.tsv` locally as
`replay.py`, and the inputs from `SOURCE.tsv` in an `inputs/` directory.
Then use:

    set -o pipefail
    sh run.sh | cmp expected.json -

The [Space source-complete archive](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80)
already materializes them. Replay uses Python 3, NumPy, SQLite WAL and Git.
Lean 4.36.0 and Mathlib check four scoped read-path lemmas in
`StationReadCut.lean`. These do not formalize SQLite or the native plant.

[Prepared vs armed succession](armed-recipient/README.md) checks when a
second candidate can take over without reaching the first, and when
an actual closure of the first candidate's publication store is required.
