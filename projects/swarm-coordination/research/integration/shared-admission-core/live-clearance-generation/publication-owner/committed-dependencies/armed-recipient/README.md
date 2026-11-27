# Replace a prepared nominee; close an armed installer

[Technical note](Prepared_And_Armed_Succession.tex). A durable selection
or a frozen donor's snapshot is not, by itself, an exclusive grant to one
next publication owner. This development experiment separates two cuts:

- The authorized selector can change the nominee before any installation
  permission is committed. Both decisions use one atomic registry row.
- Once permission is committed, an unreachable nominee can still act on
  it. A replacement needs closure at that nominee's actual effect store,
  not a change to the central selection. If the nominee already applied a
  named request, the replacement needs the closed copy from that store.

The fixture checks the original native warehouse effect, actual SQLite
fences, arm crashes, subprocess races and an independent carrier action.
It assumes honest managed workers, a single trusted registry and trusted
executor/store identities. The Lean invariant proves a finite projection,
not SQLite or physical effects. No new consensus or lease protocol,
runtime speed claim, independent mission, or contract acceptance.

Materialize files in `SOURCE.tsv` under `inputs/` and `LOCAL.tsv` beside
the scripts, or use the [Space source-complete archive](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80).
Run `sh run.sh` (the source-complete archive calls it `run-armed.sh`).
Python 3, NumPy, SQLite WAL and Git; Lean 4.36.0 + Mathlib for the optional
proof check. Do not disable assertions.
