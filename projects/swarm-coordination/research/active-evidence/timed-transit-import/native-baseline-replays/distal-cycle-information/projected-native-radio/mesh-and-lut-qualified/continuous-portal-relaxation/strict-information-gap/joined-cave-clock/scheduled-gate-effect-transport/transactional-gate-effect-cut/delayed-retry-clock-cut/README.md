# Replay an exact gate outcome after time has advanced

Civilian SQLite-owned simulation, using the unchanged gate worker and
schema from PR 883. The exact pinned prerequisites are under `up` in
the Space supplement. Requires Python 3 and Git.

```sh
bash replay.sh up | cmp - EXPECTED.jsonl
```

The disposition refers to an operation key, not the present physical
gate state or a new authorization.
