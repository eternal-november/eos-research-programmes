# Replay the moving gate and dock handoff on one clock

Civilian held-in test. Use exact Cave Circuit 01 source under `up` as
listed in `SOURCE.tsv` (Space 666; world meshes and raw LUT verified by
their pinned hashes). Bring the exact small `parent` directory listed in
`PARENT_INPUTS.tsv`; Space supplement includes it. Python 3 with NumPy
and NetworkX, SQLite, Git and C++17 are required.

```sh
bash replay.sh up parent | cmp - EXPECTED.jsonl
```

The physical slab and database workers are simulated infrastructure.
The native radio comparison is source-pinned. No gate hardware timing
or reset semantics are established. The simulation monitor terminates
an unsafe trace instead of treating a collision as reachable delivery.
