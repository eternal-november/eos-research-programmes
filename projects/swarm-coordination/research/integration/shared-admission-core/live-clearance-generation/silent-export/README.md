# Taking over after a silent migration

[Proof, outcome table and scope](Silent_Export.tex). A third local durable
store can retain the final evidence after the old process exits. A matching
seal is enough only if the prepositioned checkpoint already covers all
native state, canonical results and current rights. A bound suffix can
repair that checkpoint. A frozen donor without a durable external export
still leaves recovery blocked in the tested model.

Materialize `SOURCE.tsv`, then use Python 3.11+, NumPy, and SQLite WAL:

    set -o pipefail
    sh replay.sh /path/to/materialized-sources | cmp expected.json -

This compares local persistence and selected native effects under an
authored handoff, not an independent mission or a distributed protocol.
