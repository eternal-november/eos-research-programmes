# Issue 92: finite-free matrix dependent Fubini

The production module implements a finite-free coefficient model over an arbitrary commutative semiring. Its morphisms retain a carrier map and the full matrix out of each tagged fibre, equivalently its source-indexed columns. The Fubini comparison is natural in those morphisms. The rational shear example distinguishes contributions with equal augmentation; repeated addresses, empty fibres and zero-augmented witnesses have separate checks.

[Source and declaration crosswalk](Matrix_Fubini_Crosswalk.tex). The earlier exact author replay and dependency pins are recorded alongside it. This is a matrix instance of the source result; the noncoproduct rig case and bundled contextad calculus are separate obligations. The matrix proof uses the coproduct structure of direct sums of finite free coefficients.

## Verification

From the Lean project root, run the usual `lake build` and `lake env lean AxiomAudit.lean`. To check the positive probes and their 13 separate axiom reports after the build:

```sh
lake env bash -eu -c '
    tmp=$(mktemp -d)
    trap '\''rm -rf -- "$tmp"'\'' EXIT
    mkdir -p "$tmp/checks"
    lean -o "$tmp/checks/AugmentedMatrixFubini.olean" checks/AugmentedMatrixFubini.lean
    export LEAN_PATH="$tmp:$LEAN_PATH"
    lean checks/AugmentedMatrixFubiniAudit.lean
'
```

The files `checks/negative/ScalarProxy.lean` and `checks/negative/ZeroCarrier.lean` are intentionally rejected by Lean. Their expected diagnostics are, respectively, the unsolved goal `0 = 1` and a carrier type mismatch mentioning `noWitness.Pos`. They are excluded from the ordinary project build.
