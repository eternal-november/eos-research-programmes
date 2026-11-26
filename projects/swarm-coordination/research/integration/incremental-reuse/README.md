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
