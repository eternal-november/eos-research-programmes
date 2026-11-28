# Fixed-geometry stop reserve
Reconstruct SOURCE.tsv as in PR 855 or use the full archive. Then run:

```sh
bash replay.sh > NATIVE.txt
sha256sum -c NATIVE.sha256
python3 -B check.py NATIVE.txt | cmp - EXPECTED.json
```

The source math is the velocity-only range limiter, not the separate ROS trajectory limiter. `Stop.lean` is standalone under Lean 4.36.0.
