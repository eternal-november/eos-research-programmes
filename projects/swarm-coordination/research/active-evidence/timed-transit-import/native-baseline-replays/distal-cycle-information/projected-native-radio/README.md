# Distal Cave01 projected native radio placement sweep

Reconstruct `SOURCE.tsv` inside `up/` or use the Space archive. Requires Python 3, Git and C++17.

```sh
bash replay.sh up | cmp - EXPECTED.txt
```

The tested positions are SDF reference origins, not certified poses of moving vehicles. Physical closure, actual local sensing, and RF graph edges are separate mechanisms.
