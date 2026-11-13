# Reproduce C1 without reusing project proof objects

Prerequisites are the unchanged pinned `lean-toolchain` (Lean 4.35.0) and
`lake-manifest.json` dependencies. Install/fetch public dependencies by the
standard Lake workflow before mathematical verification. The development
machine's convenience environment was sourced from
`/workspace/shared/witnessed_B_20261024/toolchain_recovery/env.sh`; this absolute
path is NOT a required dependency of the delivered source. Public package
access/build setup is separate from proof checking. No credentials or private
package sources are included.

Run at the project root, with `lean` and `lake` on PATH:

```
bash verify_workstream_C1.sh
```

The driver checks all 299 unchanged files of the delivered A/B archive and the
frozen C1 source snapshot; runs the unchanged full A/B reproduction; compiles
all 21 inherited project modules, `GraphCoordinates`, and the new C1 module
into a NEW output directory; checks exact named axiom closures; and reruns both
the author finite checker and the nonauthor independent full-product checker.
It never writes checkpoint proof sources or replaces original result files.
Its logs and `result.json` are under `reproduction_C1/<timestamp>/`.

Project `.olean` files are generated afresh and excluded from the source
package. Installed mathlib/dependency proof objects are reused at the pinned
versions, as in the accepted A/B workflow; this is not a bootstrap rebuild of
Lean or all of mathlib. Expected resource use is a few minutes and less than
one GiB additional working space on this environment (dependency installation
may take substantially more). Exact measured timing appears in the logs.

`L` means the listed Lean declarations and their actual axiom closure.
`C` means deterministic Python finite execution, not kernel proof.
`P` means the reviewed complete mathematical proof; no program can promote
its own successful run to independent acceptance. Full C1 remains OPEN for
later C5/F2 integration even when every local check passes.
