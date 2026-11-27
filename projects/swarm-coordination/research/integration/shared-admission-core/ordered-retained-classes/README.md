# SC-ORDERED-RETAINED-CLASSES: Can the same admission rule protect a physical order after a second fault?

This second development fixture uses MRWS inventory and order-station callbacks, not RWARE or a radio sender. A is already unavailable, and the old station still needs its ordered classes. B and C previously carried two and one of the remaining classes. A second fault can remove either carrier before handoff. The spare has a shared limit on new pickups.

Four pickups suffice with a timely scoped report. In the B-loss case the old order needs all four. In the C-loss case it needs three and can stage a separate optional item. Without the report, no single full-service plan fits four slots; five suffice to reconstruct both batches. These results use class custody and prefix-ordered station acceptance, not unique-item identity or a measured driving deadline.

[Proof and comparison](Ordered_Retained_Classes.tex). Materialize the exact `SOURCE.tsv` path layout, then run:

```sh
set -o pipefail
sh replay.sh /path/to/materialized-sources | cmp expected.json -
```

The unchanged shared checker matches exact direct selection. The native callbacks establish class custody and order completion; fault delivery, authority, time cuts and pickup budget are authored. No physical trial, independently chosen mission or architecture disposition.
