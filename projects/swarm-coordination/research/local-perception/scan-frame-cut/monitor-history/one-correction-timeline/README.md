# One correction across two-stamp monitor uses

[Exact joint-history model and proof](One_Correction_Two_Stamp_Uses.tex).
Adjacent acquisition-to-use windows can each cross a possible frame correction
without any single correction that crosses both. The result tracks one shared
correction through both the evaluation and acquisition counters without
independently resampling it at each use.

From this folder, with the parent relation replay and sibling scan-use
corroboration implementation:

```sh
python3 -B timeline.py | cmp results.json -
```

The two-stamp mechanism and counter semantics come from the preceding
selected source replays. The one-correction law, timestamps, and exact
unperturbed input geometry are authored model premises.
