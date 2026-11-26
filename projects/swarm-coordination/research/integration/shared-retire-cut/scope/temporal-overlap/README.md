# Combining old occupancy at a recovery cut

A single simple temporal network with positive holds determines exactly which old work may still overlap. The maximum old load is a weighted antichain. A separate map and allocator example shows why a new version does not itself discharge old physical effects.

- [Temporal occupancy and exact inherited interface](Which_Old_Holds_Can_Overlap.tex)
- [Authored map-version and allocator contrast](Mixed_Map_And_Role_Cuts.tex)
- [Exact solver comparisons](replay.py) and [recorded results](results.json)

Run python3 replay.py and compare its output with results.json. Run python3 map_replay.py for the separate authored cut examples. The mapped case is not a stock VDA implementation test.

[Open and closed endpoints](touching/) extend the flow test to real event times and specify when a potentially empty hold breaks the order reduction.

[Shared calibration](shared-calibration/): exact joint occupancy when timed old holds also depend on one common uncertain translation.
