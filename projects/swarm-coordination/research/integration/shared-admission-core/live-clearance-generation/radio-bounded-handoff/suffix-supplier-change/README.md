# SC-SUFFIX-SUPPLIER-CHANGE: A second fault can change who owes the last radio send

The old warehouse result remains unsettled while a second fault changes which transmitter can deliver the final suffix. In this fixture the normal sender Q and the alternative P both hold the needed archive; only one path is usable at the final cut. A real registered callback at tick 7 tells the entry rule which sender can finish, and a separate registered request prepares that sender. The same shared kernel checks the two charging histories and the old duty.

When Q can transmit, defer the second four-byte diagnostic to tick 10. When Q loses the required path and P can transmit, P can carry the suffix at tick 8 and Q can finish the diagnostic at tick 7. P's good link is not enough: an extra byte of prior debit, or missing legal authority, defeats the substituted send. A notification at tick 8 is too late for the declared tick-7 preparation cut. Unrelated warehouse work continues.

[Statement and comparison](Suffix_Supplier_Change.tex). Materialize the pinned input tree in `SOURCE.tsv`, then run:

```sh
set -o pipefail
sh replay.sh /path/to/materialized-sources | cmp expected.json -
```

The fault support, selector truth and exclusive preparation rule are authored. This is a selected-source I1 development test, not a deployed failover or an independently chosen mission.
