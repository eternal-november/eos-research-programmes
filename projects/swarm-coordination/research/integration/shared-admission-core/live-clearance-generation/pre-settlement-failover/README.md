# A second route loss before native settlement

[Operating envelope, constructive proof and comparison](Pre_Settlement_Failover.tex).
A real station worker exits before or after its commit. P's route can
then fail while the station effect is still pending. A Q that actually
received and prepared the same-key authority can settle it. The source
takes the real return step only on a received qualified result.

Materialize the source pins in `SOURCE.tsv`, then with Python 3.10+,
NumPy, SQLite WAL, C++17 and a shell with pipefail run:

    sh replay.sh /path/to/materialized-sources | cmp expected.json -
