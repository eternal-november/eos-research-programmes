# Guarded fault family screen

A finite-DAG development control for the fault-stack checker, complementing
the explicit rooted model and the receiver-binding experiment. See
[the scope and proof](Guarded_Fault_Families.tex). The frozen kernel retains
one installation on every path. It reuses badness support after a qualified
restriction, and separately replays a current edge witness after guard edits.

Run `python3 -B replay.py | diff expected.txt -` from this directory.
`Guarded.lean` checks the logical core in Lean 4.35.0 (also replayed with AXLE
and its default Mathlib header). The Python uses only the standard library.
BDD live counts exclude terminals. The deterministic tests do not report
wall time or claim a gain against another incremental checker.

These are authored qualification controls, not independent validation or
fault-inventory dispositions. In particular, a reading, an effectful probe,
and an edited plant do not have interchangeable update rules.
