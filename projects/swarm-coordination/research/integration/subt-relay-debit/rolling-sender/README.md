# Rolling send windows and the first sender

[The proof and source limits](Rolling_Sender_Windows.tex).

- `node check.js | diff -u check.txt -` checks the compressed rule against
  direct enumeration. It requires only Node with standard JavaScript.
- `sh replay.sh | diff -u replay.txt -` runs the selected native source.
  Materialize the blobs listed in `SOURCE.tsv` as `src0` through `src5`
  and copy the development shim `../replay.cpp` here as
  `upstream_replay.cpp`. The complete verified Space archive already includes
  these inputs.
- `RollingSender.lean` contains the audited helper lemmas. The check used
  Lean 4.35.0 with Mathlib; the expected messages are in `lean-check.json`.

This offline author fixture tests assignments, not a live deployment or an
independently selected case.
