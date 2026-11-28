# Native radio acquisition of gate clock evidence

Civilian held-in extension of the exact #889 clock, movement and dock
case. Use the official source assets under `up` from Space checkpoint
666 and the exact included `parent` sources. Python 3 with NumPy and
NetworkX, C++17, SQLite and Git.

```sh
bash replay.sh up parent | cmp - EXPECTED.jsonl
```

Causal queue and callback times are authored simulated delays. Native
routing, frame delivery and rate admission execute source code; no
radio-clock measurement on hardware or independent selection is implied.
