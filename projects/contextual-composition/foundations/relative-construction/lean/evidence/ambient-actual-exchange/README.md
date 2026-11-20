# Actual ambient four-to-two exchange

Use the Lean subtree of the parent checkout at
`22f967a29c13b5bddea550a3b3ccf4f24b94dfae` as `PARENT_LEAN_DIR`, and the Lean
subtree of this candidate as `CANDIDATE_LEAN_DIR`. Set absolute `LEAN_BIN` and
`PACKAGES` for the pinned Lean 4.35.0 binaries and dependency checkouts.
Run from this evidence directory with fresh output paths:

```sh
python3 project-parent.py freeze/parent.json "$PARENT_LEAN_DIR" /tmp/exchange-parent
python3 prepare-overlay.py "$CANDIDATE_LEAN_DIR" /tmp/exchange-freeze
bash /tmp/exchange-freeze/replay.sh /tmp/exchange-parent /tmp/exchange-replay
```

The exact-membership assembler intentionally rejects a raw parent checkout
with extra documentation and historical evidence. Projection verifies all
259 canonical parent files. Overlay preparation verifies the 36 added source
files; assembly regenerates the audit, index and umbrella and verifies all
295 target digests. Replay checks the toolchain and dependency commits, builds
the project, and runs the ordered audit and 17 official probes. Independent
review started without prior project artifacts and reused pinned external
libraries. The additional directed-tip witness here can be checked with
`lake env lean` from the replayed project.

The theorem is the actual pre-final exchange, not a completed horizontal
pseudomonad or strict contextad recovery. See `IndependentReview.tex` for the
checked statement, counterexamples and residuals.
