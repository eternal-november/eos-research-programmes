# Recheck the physical effect of a queued closure on takeover

Held-in civilian simulator with SQLite-owned gate state, not a robot or
actuator test. Use Python 3, Git and the one hash-pinned input in `up`
(included in the Space supplement). Native cave occupancy is verified
upstream in PR 881; it is not recomputed from assets here.

```sh
bash replay.sh up | cmp - EXPECTED.json
```

Output vectors are [number of trials, contact failures under the padded
body model, approved queued requests]. The separately enabled closure
job completes in every case. No fallback for an uncontrollable collapse
is modeled.
