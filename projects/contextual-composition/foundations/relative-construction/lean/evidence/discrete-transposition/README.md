# Discrete transposition: Lean result and reproducibility

See [RESULT.tex](RESULT.tex) for the claim-to-Lean crosswalk and
[INDEPENDENT-REPLAY.tex](INDEPENDENT-REPLAY.tex) for the independent proof
and replay assessment. The result is a necessary obstruction to the stated
pure-postcomposition-compatible discrete grade presentation, not a classification
of contextads. Issue #105 is not closed.

The frozen [parent](https://github.com/eternal-november/eos-research-programmes/commit/f458186590df968a516ba73a8eb76fcf044544b0)
is the merged #236 code predating this result. Obtain that revision's
`projects/contextual-composition/foundations/relative-construction/lean` subtree
as `PARENT_LEAN`. The runner projects the 507 applicable paths, checks the
SHA-256 and Git blob hashes of their bytes, and applies the six-file locked
overlay to an empty output. The overlay is intentionally duplicated so that
reviewed candidate bytes are reproducible from the pinned parent even when
later canonical code evolves. Its three additional files give 510 output paths.

On x86_64 Linux, supply `LEAN_BIN` pointing to the official Lean 4.35.0
executables and `PACKAGES` pointing to the nine pinned package checkouts with
the matching upstream Lake/mathlib products already cached. The runner
verifies the compiler binary, version and dependency revisions; dependency
binaries are reused and the project build begins without project binaries.
The scripts neither provide nor download that external cache.

From this evidence directory:

```sh
LEAN_BIN=/absolute/path/to/lean/bin PACKAGES=/absolute/path/to/packages \
  bash freeze/replay.sh "$PARENT_LEAN" /absolute/path/to/new-clean-work
```

The new work path must not exist. The runner builds and runs the trusted-axiom
audit (4,910 ordered entries) and the 34 official probes. The reviewed audit
transcript's SHA-256 is
`b27460e71259498ed4c0c52c361180e127ab9fb7e3cdb6a7eac6d213491d411b`.
See the review for the observed independent execution, which began without
project artifacts but was interrupted and resumed twice after source,
dependency, and partial-product validation. Optional expected-failure probes
run with the same pinned Lean in PATH, passing the absolute work path:

```sh
python3 freeze/probe-controls.py /absolute/path/to/new-clean-work lake env lean
```
