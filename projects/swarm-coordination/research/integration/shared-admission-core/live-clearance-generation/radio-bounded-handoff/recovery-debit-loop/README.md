# SC-RECOVERY-DEBIT-LOOP: Can successful checks keep a failed repair from recovering?

A diagnostic can succeed at its own receiver and still delay someone else's recovery. In the pinned SubT replay, the backup transmitter starts with a charged, erased 140-byte probe. Two successful four-byte checks at an independent endpoint leave too little capacity for the 173-byte suffix needed to restore a warehouse station. Retrying the same sequence recreates the obstruction, including two subsequent attempts in the native replay.

The common admission kernel instead reserves space for the old suffix and defers just the second check until tick 10. In the positive fixture, the suffix arrives at tick 8, both checks meet their respective deadlines, and unrelated motion continues. If the second check is due by tick 9, no schedule on the same transmitter can meet all three deadlines. The same-budget direct scheduler ties.

[Model, proof, and scope](Recovery_Debit_Loop.tex). Materialize `SOURCE.tsv`; then use Python 3.11+, NumPy, SQLite WAL, C++17 and patch:

```sh
set -o pipefail
sh replay.sh /path/to/materialized-sources | cmp expected.json -
```

This is a bounded integrated counterexample and constructive service witness for the I07 mechanism, not an architecture-level inventory disposition or an independently selected mission.
