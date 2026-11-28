# One-way clock calibration in the native cave replay

Civilian held-in comparison on the same geometry and work as the
native full-echo run. Requires official cave assets from Space 666
under `up`, the pinned included `parent` sources, Python 3 with
NumPy and NetworkX, C++17, SQLite and Git.

```sh
bash replay.sh up parent | cmp - EXPECTED.jsonl
```

A one-way physical latency upper bound in this test is a supplied
timing contract, not something inferred from simulated packet delivery.
