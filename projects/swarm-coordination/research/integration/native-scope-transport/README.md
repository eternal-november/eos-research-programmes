# Consumer-scoped native transport

An unchanged two-branch policy uses actual old-settlement evidence. Its
three delivery checks survive on a replacement source at a late cut even
though the full action table differs. At the earlier cut they fail. A
separate warehouse action exposes why carrying individual witnesses
without execution identity is not enough.

[Claim and proof](Native_Scope_Transport.tex). Run with Python 3, NumPy
and C++17:

    sh native.sh ../compound-settlement /path/to/upstream | cmp expected.json -

The inherited inputs are pinned by Git blob identity in `INHERITED.tsv`
to main commit `f18e877ffde245a687daad754ae03c96338cc60d`; use the
referenced `compound-settlement` directory and its `SOURCE.tsv` to stage
the upstream files. Lean kernels `Reindex.lean` and `Scope.lean` checked
in AXLE with Lean 4.35.0 and the Mathlib header. The archived code is a
source-level developmental simulation, not an independent transfer.
