# E3 checked typed core evidence

The formal payload is the original A/B/C1/C2 core source, byte-identical accepted
E1 modules, and two new E3 modules. Read `P_CORE_ADAPTER.md` for the exact scope.
This is NOT a full formalization of the P equipment/model-comparison theorem.
The new groupoid instance has 3 objects, S3 grades and finite scalar ZMod2.
It checks actual all-arity cell restriction fibres retaining full partition
and scalar, noncommuting changes, real binary/nullary semantic generators,
the actual original Signature/Tree/Calc API, a certified N6 semantic bridge,
repeated distinct refinements and a genuinely nonfaithful scalar-erasing
Calc.Hom. No identity-map injectivity is counted as comparison evidence.

## Source-only replay

No download or installation is required. The restored compiler is Lean 4.35.0
(commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc), and only pinned public upstream
package objects are reused. The original project and all new original modules
are compiled in a fresh directory; no pre-existing project `.olean` is copied.

```
python3 verify_fresh.py \
  --toolchain /workspace/shared/d1_equivariant_transport_20261031/formal/toolchain/lean-4.35.0-linux \
  --upstream-project /workspace/shared/d1_equivariant_transport_20261031/formal/toolchain/project \
  --output /tmp/e3-replay/evidence/formal_result.json \
  --work-parent /tmp/e3-replay/work
```

Without output/work arguments the runner uses this package's `evidence/` and
`runs/`. For immutable extracted-archive replay, use external paths as above.
The dependency manifest SHA-256 is
`0e4afebb985207e83e2a2fdf3d42281f9986e939ebc31084eaa5f8c3479c22cc`;
the exact revision and clean tracked-source state of every public package is
checked. The mathlib pin is `56a005855ea17e0b0958f73ec801ae140b0a1679`.
No network commands, `lake update`, or project-cache download are performed.

The source freeze is atomic and includes this README, the P adapter, verifier,
original custody record, all bundled original source and all four E1/E3 Lean
modules. The verifier checks the complete declared source set/hash before and
after execution and checks the freeze itself did not change. Every new module
must compile without warnings or proof holes. Transitive `#print axioms`
closures allow only Lean's standard `propext`, `Classical.choice`, `Quot.sound`;
there is no custom axiom or `sorryAx` allowance. Original C1's closure audit and
the exact original E1 core comparisons are included.

## Negative tests and guards

Six semantic Lean mutations must be rejected: drop grade inverse, reverse
boundary multiplication, erase cartesian scalar, erase primitive scalar,
erase canonical local-coordinate lifts, and assign the first replacement to
both equal but distinct middle occurrences. The last two are correctly typed
algorithm mutations caught by the concrete full-cut checks. Successful object
files are restored from frozen unmutated sources at the end.

Python optimization does not disable any checks (`require`, never `assert`).
Supported modes are normal, `-O`, `-OO`; optional `--mode` must match the actual
runtime. Source-tree output/work destinations, symlink paths, hardlinked
outputs, unknown mode, mode mismatch, source mutation and freeze tampering are
rejected. Existing output is replaceable only when it is an unlinked JSON
receipt of this verifier's schema. The runner writes receipts atomically after
all checks; a rejected guard never writes a success receipt. Guard tests use
copies/temporary files, not modifications of accepted historical sources.

## Distribution allowlist

Include `original_source/`, the four E1/E3 `.lean` files, `verify_fresh.py`,
`README_FORMAL.md`, `P_CORE_ADAPTER.md`, `original_source_custody.json`,
`source_freeze.json`, `test_formal_guards.py`, and selected `evidence/` receipts
and logs. Exclude `development_project/`, `development*.log`, `runs/`, compiler
binaries/archives, upstream packages/cache, and all generated `.olean` files.
The Python finite model suite in `../checks/` has a separate source freeze and
receipt. P correctness, finite exhaustive coverage and L coverage are distinct.
