# Timed support handoff with live loads

When relief requires a second crew to finish an old load transfer, a later authorization and a longer transfer can each fit the deadline alone but miss it together. An already authorized order lets the dispatcher send a permit earlier without letting any crew act before activation. The repair does not cover surprise orders.

The frozen receiver comparison keeps the named receipt and support reads, not just the final relief time. An independently selected store-and-forward bridge preserves those reads. Opening it one tick later fails the authorization test and loses timely service in two of the twelve scenarios that the ordinary target serves in eleven. The modular direct proof agrees in the positive case with fewer proof obligations; no proof-work saving is established.

## Proofs and checks

- [Reached cuts, cascade, and scoped repair](swarm-c11-primary/Primary_Cascade.tex)
- [Frozen receiver proof, domains, and comparison](swarm-c11-interface/Receiver_Interface.tex)
- [Independent selection and proof transfer](swarm-c11-transfer/Transfer.tex) · [Selection](swarm-c11-transfer/SELECTION.txt)

From this directory run:

```sh
(cd swarm-c11-primary && sha256sum -c SHA256SUMS && python3 -B replay.py | cmp results.json)
(cd swarm-c11-interface && sha256sum -c SHA256SUMS && python3 -B interface.py | cmp checks.json)
(cd swarm-c11-transfer && sha256sum -c SHA256SUMS && python3 -B transfer.py | cmp results.json)
```

The results establish a cascade, a repair under the stated precommitment law, and a receiver proof transfer for this finite simulated plant. They do not establish a whole-plant equivalence or complete v0.5 cascade acceptance.
