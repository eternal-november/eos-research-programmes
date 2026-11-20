# Ordinary pure insertion and covariant representable recovery

The actual pure insertion is a pseudofunctor from the ordinary base to
the representable Kleisli bicategory, with specified native pure-map and
directed bending comparisons. The covariant content comparison is on
corepresentables; its 1-cell opposite leaves native 2-cell direction
unchanged. The native binary operation is identified on objects and
arbitrary cells under the stated chart.

The two checked presentations of the ordinary pure binary comparison
are not yet identified by a chart-erasing equality. A separate covariant
pure wrapper and a direct ambient covariant comparison beyond the
checked chart are also not claimed.

Use the Lean subtree from parent commit
`aa9d87c7027ecaf2a880410bcd797c861af1a813` as `PARENT_LEAN_DIR`, and this
commit's Lean subtree as `CANDIDATE_LEAN_DIR`. Set absolute `LEAN_BIN`
and `PACKAGES` for pinned Lean 4.35.0 and dependency checkouts. Run from
this evidence directory with fresh output paths:

```sh
python3 project-parent.py freeze/parent.json "$PARENT_LEAN_DIR" /tmp/pure-covariant-parent
python3 prepare-overlay.py "$CANDIDATE_LEAN_DIR" /tmp/pure-covariant-freeze
bash /tmp/pure-covariant-freeze/replay.sh /tmp/pure-covariant-parent /tmp/pure-covariant-replay
```

Projection checks 468 parent files. Assembly adds 20 new production
modules and two new probes, regenerates the umbrella, audit and index,
and checks 490 final source hashes. Replay checks the toolchain and
dependency pins, builds the project and runs 4,724 audits and 31 probes.
