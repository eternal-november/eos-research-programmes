# Native queued route changes before dispatch

Reconstitute `SOURCE.tsv` as `up/` (or use the complete Space archive). Requires C++17, Python 3 and Git.

```sh
bash replay.sh up | cmp - EXPECTED.txt
```

Columns: queued P; queued P then Q; local P-first; local Q-first; queued auxiliary then P then Q; queued Q then P. The three vectors count old suffix deliveries, auxiliary deliveries, and wasted old-suffix transmit bytes, respectively. Solver coverage is pinned serial radio behavior, with a proposed receiver-side hook and separately declared ready copies.
