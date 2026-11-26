# Keyed, restartable publication of native warehouse transitions

[Contract, proof, comparator and limits](Native_Commit.tex). A SQLite
transaction publishes a deterministic native simulator step and its keyed
receipt together. Actual fresh subprocesses exit before and after commit;
the fresh-process retries are compared with a clean single native step.
This design applies only when the store is the publication authority for
the simulated plant.

Materialize the exact pinned files in `SOURCE.tsv`, then use Python 3.10+,
NumPy and SQLite WAL with a shell with pipefail:

    sh replay.sh /path/to/materialized-sources | cmp expected.json -
