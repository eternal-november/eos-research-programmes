# Exact old return across a native supplier change

Build the inputs listed in `SOURCE.tsv` under `up/` (or use the complete Space archive). Python 3 with NumPy/NetworkX, C++17 and Git are required.

```sh
bash replay.sh up | cmp - EXPECTED.json
```

Each scenario has a pair of vectors for fixed queued replication and cut-local admission. A vector contains [runs, exact keyed returns, independent P auxiliary completions, Q-transmitted exact returns, old-suffix transmit bytes charged without delivery]. Wire costs include both early attempts; the persisted preparation/authorization facility is held fixed and not priced. The serial pre-dispatch seam is instrumented and is not exposed by the stock broker.
