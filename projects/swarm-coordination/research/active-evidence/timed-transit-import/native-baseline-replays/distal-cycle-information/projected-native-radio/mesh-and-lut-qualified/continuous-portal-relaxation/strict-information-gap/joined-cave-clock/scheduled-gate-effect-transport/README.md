# Gate effects that survive a controller replacement

Held-in, finite, known-schedule civilian cave model. Requires Python 3.10+
and the three small pinned files in `up`. `SOURCE.tsv` records the exact
revision, repo path and Git blob for each parent input. The Space bundle
includes all three.

```sh
bash replay.sh up | cmp - EXPECTED.jsonl
```

This does not simulate the gate hardware or the authority/journal
protocol. It inspects exact physical occupancy windows for the saved
trajectory and evaluates a dynamic closure-effect model over them.
