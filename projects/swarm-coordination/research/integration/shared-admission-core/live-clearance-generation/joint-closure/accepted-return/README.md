# Same restart, different outstanding right

A durable acceptance can survive a station restart even when no motion or completion does. The pinned motion and transport replay shows both why an empty bay is insufficient and why announcing the live right can consume the receiver space its eventual release needs.

- [Executive mechanism, finite evidence and limits](Return_Authority_Cut.tex)
- `ReturnCut.lean`: simple silence and headroom facts checked in Lean 4.35.0 + Mathlib.
- Materialize exact `SOURCE.tsv` blobs under INPUT. Run `sh replay.sh INPUT > actual.json`, then `cmp expected.json actual.json`. Requires Python 3, Git and C++17.

This is a joined development fixture. The durable right, issuer closure and route policy are explicit authored instrumentation, not declarations about a stock simulator or robot. No independent holdout was used.
