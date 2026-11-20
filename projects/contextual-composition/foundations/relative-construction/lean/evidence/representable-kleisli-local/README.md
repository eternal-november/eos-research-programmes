# Directed local comparison on representables

The strong Yoneda equivalence applies to arbitrary strict Cat-valued targets.
Its representable Kleisli specialization recovers native directed structured
arrows, including noninvertible grade maps, and compares the actual unit and
composition with the native formulas. The result covers the two horizontal
cell columns, both unitor naturality laws, the mixed-endpoint triangle, and
naturality of the associator in its first modification variable. The other
two associator variables, the mixed pentagon, and the assembled bicategorical
comparison are separate obligations.

Use the Lean subtree of the parent checkout at
`15faa31bb5fbf4f92a3676e4e89771d7f7074070` as `PARENT_LEAN_DIR`, and the
Lean subtree of this candidate as `CANDIDATE_LEAN_DIR`. Set absolute
`LEAN_BIN` and `PACKAGES` for the pinned Lean 4.35.0 binaries and dependency
checkouts. Run from this evidence directory with fresh output paths:

```sh
python3 project-parent.py freeze/parent.json "$PARENT_LEAN_DIR" /tmp/representable-parent
python3 prepare-overlay.py "$CANDIDATE_LEAN_DIR" /tmp/representable-freeze
bash /tmp/representable-freeze/replay.sh /tmp/representable-parent /tmp/representable-replay
```

The projection checks the exact 385-file parent; overlay preparation collects
42 added Lean files, including four regression probes. The assembler
regenerates the aggregate imports, theorem index, and axiom audit. Replay
verifies all 427 final source hashes, checks dependency pins, builds the
project, and runs the ordered audit and all 27 official probes.

`RESULT.tex` is the author report with two TeX parameter markers corrected so
the named declarations and lock digest render verbatim. The source manifest
and Lean files were not changed by this correction.
