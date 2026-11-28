# Certified ideal timing lift

Requires the exact paths.json and EXPECTED.jsonl from PR 874, as identified
by PARENT_INPUTS.tsv. The Space supplement includes those two small files.
These results are for a translating axis-aligned body, not actual flight.

```sh
bash replay.sh up | cmp - EXPECTED.json
```
