# A retry follows a changed publication owner

[Migration law, countermodels and scope](Publication_Owner.tex).
Two separate durable stores and native simulator workers show why a
move must preserve both publication authority and completion identity.
Synchronized negative controls separate an old snapshot, omitted
completion metadata, and a still-live old owner.

Materialize the pinned files in `SOURCE.tsv`. With Python 3.11+,
SQLite WAL and NumPy:

    set -o pipefail
    sh replay.sh /path/to/materialized-sources | cmp expected.json -

A native SQLite migration calibration, tied with an equally informed
direct rendezvous rule. It does not implement distributed consensus,
physical-effect migration or an independent swarm mission.
