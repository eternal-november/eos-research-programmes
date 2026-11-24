# Mission-wide risk after a cap change

[Statement and proof](Exposure_Profiles_And_Risk_Caps.tex). Under the fixed latent-law model, a tighter cap makes future admissions depend on which sites were already exposed, not merely how many.

- `python3 replay.py | cmp replay.txt`: exact rational comparison over 18,324 queries.
- `lake env lean ExposureProfiles.lean` in Lean 4.35.0 with Mathlib: binomial cardinality, robust admission, state lower bound and cap-change theorems checked without `sorryAx`.

This is a scoped R4/L2 result and reduction to classical indexing. It neither advances communication complexity nor closes the risk track.
