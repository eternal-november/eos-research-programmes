# Full-graph cave information cutoff

Reconstitute the pinned `SOURCE.tsv` inputs as `up/` or use the Space archive. Requires Python 3 and Git.

```sh
bash replay.sh up | cmp - EXPECTED.json
```

This computes an exact result over legal abstract graph walks, not every continuously collision-free physical route. Timing, closures and the state-disclosing sensor are declared.
