# Incremental recovery proof reuse

Frozen first finite checker for exact old reach reuse. Separate judgments
cover safety, deadline, action realizability, and unresolved installations.
The direct rooted-witness worklist is a strong comparator, and the cone
checker does not generally improve on it.

    python3 -B replay.py | cmp results.json -

Only Python standard library is needed. DirtyCone.lean checks the exact
reach cut with Lean 4.35 + Mathlib. Incremental_Reuse.tex states the
scope. FREEZE.txt and reuse.py are the pre-scenario freeze. The authored
benchmarks are not independent test selection.

[Upstream change producer](patch-producer/README.md): equal compiled rows can acquire a different source dependency. Preserving that dependency makes the next finite edit check sound at matched inputs.

[Indexed witness receiver](indexed-repair/README.md): removes whole-map rebuilds in the sparse sequence, and compares both detailed counted work and a separate local pipeline timing sample against the previous worklist.
