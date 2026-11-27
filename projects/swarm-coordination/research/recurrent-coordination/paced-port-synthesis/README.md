# Paced recurrent handoffs with fixed port configuration

For this restricted corridor family, a finite relation is enough to
synthesize each local controller or prove infeasibility. Every job changes
its actual certifier, adjacent handoffs can overlap, and no global clock or
reset is needed. The first impossible saturated intervals come from
shared ports, not a timeout imposed on the search.

[Model, construction, infeasibility and replacement](Paced_Handoff.tex).
This is a modeled family with a bounded-duration local effect/latch
primitive, not an implementation for arbitrary faults or the full moonshot.
Runtime treats configured ports as fixed while jobs are offered.

    python replay.py | cmp expected.json -

`PacedHandoff.lean` was checked on Lean 4.35 without `sorryAx`.
