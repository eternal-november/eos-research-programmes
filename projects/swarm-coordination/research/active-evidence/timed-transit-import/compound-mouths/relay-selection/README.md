# Relay selection depends on passage access and outstanding reports

[Technical note](Route_Selection_Is_Not_Monotone.tex). Held-in source-law check
on the already-viewed Cave Circuit 01; no full simulator, deployed packet or
independent mission result.

Use columns 2–4 of `SOURCE.tsv` to retrieve pinned original files under the
names given in column 1. For `launch-link.txt`, use the symlink's Git blob
contents literally (not its dereferenced target or an added newline).
Place them beside the replay. It checks column 5 (Git blob ID) before use.

    node replay.mjs | cmp - expected.json

The four arithmetic statements in `RelaySelection.lean` passed Lean 4.36.0
with Mathlib and printed axioms without `sorryAx`.
