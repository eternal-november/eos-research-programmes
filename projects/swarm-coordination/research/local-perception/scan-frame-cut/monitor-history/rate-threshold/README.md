# Critical shift rate for a monitor history

[Proof and model limits](Critical_Shift_Rate.tex). Exact interval
propagation locates the first rate that can change a latch outcome.
A three-frame case passes all pairwise checks at rate 0.75 but does
not release even at rate 1; equality fails at an open endpoint.

From this directory with the parent monitor-history module present:

```sh
python3 -B rate.py | cmp results.json -
```

`FiniteSelection.lean` checked on AXLE `lean-4.35.0` with Mathlib
and no `sorryAx` (propext, Classical.choice, Quot.sound only).
The exact strict-endpoint proof and Python replay are separate.
The rate envelope is declared, not a measured controller behavior.
