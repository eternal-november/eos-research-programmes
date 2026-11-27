# Live source and scoped receipt reuse

[Native cut comparison and scope](Live_Archive.tex). Uses the parent pinned scorer and warehouse archive harness without changing its reader. Native work advances on the same SQLite WAL source while an old read view remains open. The preserved receipt can answer the past-result query, but neither a repeated absence nor a held receipt establishes a different current plant fact.

With the parent source inputs materialized, copy this `live.py` alongside `archive.py`, then run `OPENBLAS_NUM_THREADS=1 python3 -B live.py | cmp expected.txt -` with this expected output available. The Space archive contains both packages and was replayed from a fresh extraction. No hardware data or independent acceptance.
