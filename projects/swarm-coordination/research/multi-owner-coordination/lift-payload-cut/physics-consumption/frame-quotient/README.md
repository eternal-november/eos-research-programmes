# Frame evidence for scoped world intents

[Exact interface and proof](World_Intents_And_Frame_Observation.tex).
This finite model starts from the local-to-world conversion exercised in
the selected physics replay, but adds a separate attributed-effect law.
It does not claim the stock setter reports provenance or enforces authority.

```sh
set -o pipefail
python3 -B frames.py | cmp results.json -
```

`FrameQuotient.lean` checked via AXLE `lean-4.35.0` with Mathlib.
Its pairwise inverse-equivalence theorem reported only `Quot.sound`.
