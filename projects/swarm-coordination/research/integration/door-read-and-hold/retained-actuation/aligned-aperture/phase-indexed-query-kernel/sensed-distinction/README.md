# Acquire an exact source distinction without reading the private command depth

Populate `up/` with the pinned `SOURCE.tsv` blobs or use the Space archive. Python 3, Git and C++20 are required; Lean 4 for `Read.lean`.

```sh
bash replay.sh up | cmp - EXPECTED.json
lean Read.lean
```

The pose and read-error laws are simulated. Fresh categorical mode, calibrated numeric readings and numerical-only reads with a common unknown bias are different observation interfaces.
