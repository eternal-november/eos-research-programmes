## Repeated custody handoffs

On any finite path, adjacent custody transfers can compete for the same station port while each edge keeps only a bounded amount of state. An authentic receipt distinguishes the current physical clearance from retained copies with exactly `floor(L/2)+1` tag values when receipt age is bounded by `L` completed local transfers and the authorized signer alternates. With no age bound, an old genuine receipt can look fresh. The guarantee requires a reliable two-ended local gate and independently stated progress premises. This is a restricted moonshot baseline, not general compositional synthesis.

[Model and proof](Handoff_Receipt_Epoch.tex) · [Lean arithmetic and lower bound](ReceiptEpoch.lean)

From this directory, using Python 3 and Lean 4.35 with Mathlib:

```sh
for check in alternating recurrence statecheck; do
  python3 -B "$check.py" | cmp "$check.txt" - || exit 1
done
lean ReceiptEpoch.lean
```

`alternating.py` checks the general signer-window characterization. `recurrence.py` simulates repeated physical custody changes and a retained-copy counterexample. `statecheck.py` independently enumerates the finite products for the smallest paths; it tests safety and the absence of deadlocked admitted work, not fair progress under arbitrary scheduling.
