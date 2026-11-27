# MRWS partial salvage can strand an old order

A pinned, selected-source development example of two successful local
operations with a failed joint obligation. The station can accept class 4
and the replacement can later pick class 5, yet the order cannot finish
through append-only service. The rejected deposit empties its donor
before failing. A named buffer preserves the old continuation with
three instead of four pickups when the read confirms custody.

[Model, proof, limits and matched alternatives](Partial_Salvage.tex).
See [SOURCE.tsv](SOURCE.tsv) for exact input files, repository pins and
expected Git blob hashes. Put those inputs in one directory at the
relative paths in its first column. Then:

    sh replay.sh /path/to/inputs | cmp expected.json -

The 18 native callback cases use authored release times, grants, read
delivery and staging access. They are not full navigation runs. The same
frozen admission kernel and exact direct rule agree on all 12 local views.
The fourth-pick and authorized compensation arms are kept, along with
retained failed-carrier inventory and the unconsumed buffer when notice is
lost. No independent holdout, field claim, or architecture-level
inventory disposition is made.
