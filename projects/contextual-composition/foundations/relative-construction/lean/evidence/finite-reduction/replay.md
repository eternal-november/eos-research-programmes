# Replaying the finite reduction proofs

The 13 files listed in `source.json` contain all project modules used by this development. The other imports belong to Lean and the locked dependencies. On native Windows, Lean 4.35.0 and Lake compiled these files in a fresh project build directory, with verified dependency checkouts and their caches available. The package verifier and ordered audit both passed for 199 declarations. The recorded counts are 120 uses of `Quot.sound`, 108 of `propext`, and 93 of `Classical.choice`; an export can use more than one. The compiler output agreed declaration by declaration with [the recorded transcript](axioms.log). [Lake build output](scoped-build.log)

From the main Lean package directory, prepare the projection in a **new** directory. The helper checks Git-normalized SHA-256 values for every source, the toolchain, the Lake configuration and manifest, and both verification programs. It preserves the order of the scoped package imports and audits.

```sh
python -X utf8 evidence/finite-reduction/prepare_replay.py /absolute/path/to/new-finite-reduction-replay
cd /absolute/path/to/new-finite-reduction-replay
lake exe cache get Mathlib.Algebra.BigOperators.Group.Finset.Sigma Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Basic.Real.Basic Mathlib.CategoryTheory.Comma.Over.Basic Mathlib.CategoryTheory.Types.Basic Mathlib.LinearAlgebra.Prod Mathlib.LinearAlgebra.Quotient.Basic
python -X utf8 verify.py
python -X utf8 audit.py
```

Use `PYTHONUTF8=1` on Windows so that verifier subprocesses also read compiler output as UTF-8. The ordinary package-wide replay uses the same verification programs in the full Lean package directory.
