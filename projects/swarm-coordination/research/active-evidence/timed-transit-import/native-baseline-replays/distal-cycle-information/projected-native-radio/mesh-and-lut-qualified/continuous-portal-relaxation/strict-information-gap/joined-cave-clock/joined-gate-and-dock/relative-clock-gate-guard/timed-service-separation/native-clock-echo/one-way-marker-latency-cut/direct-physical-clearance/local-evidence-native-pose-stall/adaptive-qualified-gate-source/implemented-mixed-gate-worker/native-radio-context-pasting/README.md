# Native radio context projection and same-cut resource composition

Civilian logic exercise using pinned SubT application/broker code and
the existing replay simulator. Exact `up` sources are hash-pinned in
`SOURCE.tsv` and included in Space. Use Python 3, C++17 and Git.

```sh
bash replay.sh up | cmp - EXPECTED.txt
```

Fixed endpoint identities/capacity and stable epoch. The static
links and cuts are fixture inputs, not deployed radio measurements
or an independent mission.
