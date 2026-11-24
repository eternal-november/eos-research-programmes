# Timely clearance under partner substitution

In a finite warehouse maintenance model, old jobs keep a physical reservation across an instrument replacement. The installed receiver keeps its dispatch rule and safety/deadline proof when a partial sensor bank certifies a clear lane in time. An instrument sending exactly the same certificate a tick later passes standalone but cannot guarantee joint service.

The exact minimum for one lane is (r+1) distinguishable timely reports when any (r) old lanes can be held. An atomic bundle changes the minimum; the note gives an exact covering formulation and the closed two-lane case. Direct menu enumeration and the factored assume-guarantee comparison agree with the contextual claim. This does not establish general C4 acceptance, Lean verification, or physical readiness.

[Proof and model](Certified_Lane_Substitution.tex) · [Checker](replay.py) · [Expected output](results.json)

From this directory: `python3 -B replay.py --verify | cmp results.json`.
