# SC-NATIVE-APPOINTMENT-CUT: Does a simulator's final state tell us what an appointment depended on?

This reuses the exact frozen receiver from the preceding causal-order study. A managed RWARE worker crashes around a durable step. Before that original request is retried, a separate SQLite owner reads its keyed receipt and writes an appointment. The owner can optionally disclose whether the recorded appointment depends on that named step. The grant text is unchanged.

When the crash rolls the step back, the separate owner sees no receipt before appointing. When the crash happens after commit, the owner sees the receipt. Retrying the same request leads to exactly the same source simulator state in both cases. The second appointment cannot support the rescue under the authored charter, which needs a common historical cut before the old step. Matching an anonymous step at the same tick instead of the named result wrongly withholds a permissible rescue in the sibling case.

The consuming fixture actually runs selected native RWARE movement only if the historical check, the newly granted scoped authority, current operating authority, and the current berth occupancy all allow it. The unrelated fixture continues. This is a selected-source calibration, not standard RWARE governance, integration acceptance, a measured network protocol, or an independently chosen transfer.

[Proof and assumptions](Native_Appointment_Cut.tex). Materialize exact pinned files in `SOURCE.tsv` into a sources directory, then run:

```sh
set -o pipefail
sh replay.sh /path/to/sources | cmp expected.json -
```
