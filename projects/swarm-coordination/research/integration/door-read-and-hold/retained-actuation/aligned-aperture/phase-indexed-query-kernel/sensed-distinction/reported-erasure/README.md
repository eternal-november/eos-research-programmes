# Erasure feedback at the native aperture read cuts

Populate `up/` with the pinned `SOURCE.tsv` blobs or use the Space archive. Python 3, Git and C++20 are required.

```sh
bash replay.sh up | cmp - EXPECTED.json
```

Expected results contain fixed and erasure-contingent schedules. Fixed refutations give schedule, erased time, conflicting zero-indexed history IDs and a common transcript in quarter-deficit units.
