# Exact receipt value projection across a native cut

Reconstruct the exact inputs in `SOURCE.tsv` as `up/`, or use the Space archive. Python 3 with NumPy/NetworkX, C++17 and Git are needed. Proof: Lean 4, core only.

```sh
bash replay.sh up | cmp - EXPECTED.json
lean Projection.lean
```

Results record [runs, suffix attempted, suffix delivered, suffix decoded, exact installation and restart, diagnostic 2 at tick 7, decoded but rejected]. A typed refusal for a missing join, an application refusal for corrupted data, and the absence of a suffix callback are different. The reported transport optimization is conditional on this archive type and already-agreed format.
