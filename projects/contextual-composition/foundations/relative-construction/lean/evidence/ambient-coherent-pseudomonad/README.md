# The ambient coherent pseudomonad

Use the Lean subtree of the parent checkout at
`2c45ffcd765253b42de92eac98968595a00a661f` as `PARENT_LEAN_DIR`, and the Lean
subtree of this candidate as `CANDIDATE_LEAN_DIR`. Set absolute `LEAN_BIN` and
`PACKAGES` for the pinned Lean 4.35.0 binaries and dependency checkouts.
Run from this evidence directory with fresh output paths:

```sh
python3 project-parent.py freeze/parent.json "$PARENT_LEAN_DIR" /tmp/pseudomonad-parent
python3 prepare-overlay.py "$CANDIDATE_LEAN_DIR" /tmp/pseudomonad-freeze
bash /tmp/pseudomonad-freeze/replay.sh /tmp/pseudomonad-parent /tmp/pseudomonad-replay
```

Projection verifies the 295 manifested parent files while excluding unrelated
checkout files. Overlay preparation verifies the 90 added source paths. The
assembler regenerates the umbrella, theorem index and axiom audit and updates
the audit name parser to handle primes; it verifies all 385 final digests.
Replay checks the toolchain and dependency pins, builds the project and runs
the complete ordered audit and all 23 official probes.

The original left, right and associativity naturality squares hold on arbitrary
ambient strong arrows. The actual triangle and pentagon correspond, separately,
to the original native triangle and pentagon laws. The bundle does not assert
representable Kleisli comparison or structured-arrow recovery.
