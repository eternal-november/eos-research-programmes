# Supplier migration and queue-cut rewind

An indexed sender check transports the conservative FIFO budget under certified queue edits, receiver growth and a cross-sender migration. If the newest protected row moves, the earlier cut can need order information that the old frontier had no reason to expose.

- [Invariant, counterexample and costs](Queue_Cut_Rewind.tex)
- `Rewind.lean`: checked finite witness, Lean 4.35.0 and Mathlib.
- Replay with `python3 -B replay.py | cmp expected.json -` (stdlib only).

14,400 model checks against full recomputation. The predecessor experiment observes real selected broker callbacks; this study models lawfully published edits. It does not treat a native dequeue as withdrawal or infer physical delivery from available sender credit.
