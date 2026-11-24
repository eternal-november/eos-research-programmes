# C11 independent bounded receiver transfer

Run with the sibling frozen `swarm-c11-primary` and `swarm-c11-interface` packets available. The selection was written and pinned before running a comparison or reading the frozen result data.

```sh
cd swarm-c11-transfer
sha256sum -c SELECTION.SHA256
sha256sum -c SHA256SUMS
python3 -B transfer.py | cmp results.json
```

Default replay rederives all traces and maps and byte-checks both without writing them. Explicit `--export` regenerates `traces.json` and `maps.json` only. Read `Transfer.tex` for the witness, exact quotient argument and direct comparison. On the review environment the standard-library replay took about three seconds; this is not a benchmark. Scope is one in-flight root permit, a one-slot relay, deterministic reliable delivery, two initial load prefixes, two dwell settings and deadlines 4–6. Queue contention/overflow, retransmission, non-atomic observations, dynamic topology, larger loads and physical deployment were not tested.
