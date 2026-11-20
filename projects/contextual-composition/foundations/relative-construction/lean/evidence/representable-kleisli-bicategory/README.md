# Directed representable Kleisli bicategorical comparison

The exact mixed-endpoint pentagon and all three associator naturality
columns assemble the original representable Kleisli bicategory.
The native structured-arrow comparison is a pseudofunctor whose hom
functors are the original equivalences and whose object map covers the
tagged representables. The native units and entire composition functors
agree with the existing operational ones. There is no claim about
coverage of the full presheaf carrier or a chosen inverse pseudofunctor.

The actual pure unit and associativity paths check, but the ordinary-base
equality fields and the assembled pure pseudofunctor remain open.

Use the Lean subtree of the parent checkout at
`b4fb94dfc7d9599087ee4232e7f477da6530d1da` as `PARENT_LEAN_DIR` and the
Lean subtree of this candidate as `CANDIDATE_LEAN_DIR`. Set absolute
`LEAN_BIN` and `PACKAGES` for the pinned Lean 4.35.0 binaries and dependency
checkouts. Run from this evidence directory with fresh output paths:

```sh
python3 project-parent.py freeze/parent.json "$PARENT_LEAN_DIR" /tmp/representable-bicategory-parent
python3 prepare-overlay.py "$CANDIDATE_LEAN_DIR" /tmp/representable-bicategory-freeze
bash /tmp/representable-bicategory-freeze/replay.sh /tmp/representable-bicategory-parent /tmp/representable-bicategory-replay
```

Projection checks 427 parent files. The assembler uses 39 new production
modules and two new probes to regenerate the umbrella, audit and index, and
checks 468 final source hashes. Replay checks the toolchain and dependency
pins, builds the project, and runs 4,578 ordered audits and 29 probes.
