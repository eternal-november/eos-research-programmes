# Time-valid transit actions on an imported cave graph

[Technical note](Timed_Transit_On_Imported_Graphs.tex). The normalized
`development-topology.json` is the already-viewed natural/01 planar grid
from the pinned SubTGraph source, excluded from independent evaluation.
See `UPSTREAM_SUBTGRAPH_LICENSE`. It has 244 occupied cells and 21
independent cycles. This is generated topology; travel time, closures,
probe feeds and radio-slot law in the fixture are separate assumptions.

Run from this directory:
```sh
python3 -B replay.py | cmp real-replay.txt
python3 -B robustness.py | cmp robustness.txt
PYTHONPATH=../inspection-event-adapter python3 -B fixture_adapter.py | cmp fixture-replay.txt
```

The backup archive includes the matching adapter core under
`adapter-377/`; substitute `PYTHONPATH=adapter-377` there. The normalized
topology is directly replayable; the original serialized blob is not shipped.
The optional `import_topology.py` checks that source's simple numeric
wire shape without executing it. Use ordinary Python mode.

Lean 4.35.0 with Mathlib checks `TransitWindow.lean`: the fixed-offset
obstruction and attainable integer-offset box arithmetic. The critical
scope is no decision, observation, waiting, reversal or other material
effect inside a committed macro action. The code does not claim such
contraction is correct for arbitrary crew control.

[Effective cave radio model](effective-radio-model/README.md): cave asset
calibration must verify which model and lookup table actually loaded.
