# A recovery-induced support handoff cascade

An already accepted rack inspection and a downstream transfer can need the same lane. A routine retry blocks the transfer only after an authorization delay puts it in the retry's slot. The same trial with an independent inspection lane removes the conflict but adds capacity; the actual repair sends the preauthorized permit earlier without adding a lane.

[Proof, comparisons and remaining review](Recovery_Lane_Cascade.tex) · [Model envelope](FROZEN_DESIGN.md) · [Fault register](FAULT_REGISTER.md)

```sh
sha256sum -c SHA256SUMS
sha256sum -c FREEZE.SHA256
python3 -B replay.py | cmp results.json
python3 -B boundary.py | cmp boundary.json
```

The first checker replays the second workload on the pinned primary engine and matches it to a separate schedule enumeration. The second recomputes the original receiver's factor tests over actual executions on the one-tick-dwell subcarrier. This authored workload is not a held-out transfer.
