# Retained material after station downtime

[Source audit and model](Retained_Work_And_Factory_Downtime.tex) · [Lean arithmetic](CollectionDeadline.lean)

- Rulebook source: `robocup-logistics/rcll-rulebook`, `rulebook.tex`, Git blob `e2caa064fbc4836f63c368d4da38b31546af39dd`.
- [Published benchmark folder](https://github.com/robocup-logistics/rcll-refbox/tree/master/benchmarks): `rcll100.gz`, Git blob `b54f8c7ba3f6ee4765d49f99013466275009d414`, compressed SHA-256 `6336be1e56339981a9235edf94a6fc67bef7d93f4fb0a041b376f79256f5773e`. The raw archive is not republished here.

From this directory after obtaining the official compressed benchmark:

```sh
set -o pipefail
python3 -B archive_audit.py rcll100.gz | cmp archive-audit.txt -
python3 -B coverage.py rcll100.gz | cmp coverage.txt -
python3 -B source_model.py | cmp source-model.txt -
lean CollectionDeadline.lean
```

The model can be replayed without the external archive. Lean 4.35.0 with Mathlib checks timing proofs, not the source instruments. The source audit concerns the pinned archive only. The development fixture is not an official game replay or independent transfer.
