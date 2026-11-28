# Receiver-local old supplier probe
Reconstruct SOURCE.tsv (target, repository, commit, source path, Git blob) under `up/` or use the complete archive. Requires Python 3 with NumPy and NetworkX, C++17 compiler, Git and patch.

```sh
bash replay.sh up | cmp - EXPECTED.json
```

The timeline replaces the original authored mode message with a native receive observation, under an explicit assumption about when that observation is closed and about the shared local preparation role.
