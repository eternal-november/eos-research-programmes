# MRWS retained loads after a battery fault

[Model, native source boundary, and bound](Retaining_Unsettled_Loads.tex).

Use MRWS commit 941338e9ea4c4eaebb87f8374f80fd576497ad01. The minimal
native files and their Git blob digests are in upstream-blobs.txt.
Set PYTHONPATH to its simu directory. No genetic or Unity runtime is used.

```sh
set -o pipefail
PYTHONHASHSEED=0 PYTHONPATH=/path/to/MRWS/simu python -B replay.py | cmp result.txt -
```

The runner compiles selected unchanged Python function bodies and
imports the native inventory and station. It drives six explicit
cut-level callback traces, not full warehouse trajectories. The 2,005
additional checks enumerate the cost bound across loss sets.
