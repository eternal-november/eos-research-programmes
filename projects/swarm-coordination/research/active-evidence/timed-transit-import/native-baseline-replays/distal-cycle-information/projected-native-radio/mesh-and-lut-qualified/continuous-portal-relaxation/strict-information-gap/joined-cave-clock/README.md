# Physical gate binding (corrects PR 877)

Requires the pinned Cave Circuit 01 assets from Space 666 and the small parent supplement from Space 671, or exact reconstruction from PARENT_INPUTS.tsv.

```sh
bash replay.sh up parent | cmp - EXPECTED.jsonl
```
