# Live endpoint growth at a protected prefix

A single receive binding changes the sender cost of already queued work. The change can be harmless for one protected report but consequential for another. The insertion guard checks both and tests actual receiver callbacks; it does not rely on an assumed stable fanout.

- [Prefix increment law and limits](Binding_Impact.tex)
- `Binding.lean` checks the finite-sum increment and inequality reductions using Lean 4.35.0 and Mathlib.
- Materialize the exact paths in `SOURCE.tsv` under INPUT. Run `sh replay.sh INPUT > actual.json`, then `cmp expected.json actual.json`. Requires C++17, Python 3 and Git.
- 576 native selected-source rows; no held-out mission, stock deployment or wall-clock progress claim.
