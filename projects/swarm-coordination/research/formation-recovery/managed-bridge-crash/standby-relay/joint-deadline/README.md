# A joint relay deadline cannot be checked recipient by recipient

A relay must remain within one existing link region while it moves to serve a recipient named by a delayed report. In this model, any two of the three possible recipients can be covered by a standby chosen for that pair. At the same deadline, no standby or common motion covers all three. With the pinned initial positions, the time after the report rises from about 0.55105 simulation units for the hardest pair to 0.57816 for the triple. At 0.57, the answer changes.

The [proof](Relay_Deadline.tex) gives the exact deadline for any finite family of closed service regions inside a common compact convex region, with isotropic acceleration and speed limits and a required stop at delivery. It permits a common nonzero velocity when the report arrives. If each service region is convex, subsets of at most \(d+1\) worlds suffice in dimension \(d\); a regular simplex shows why fewer do not suffice in general. An ordinary enclosing-ball solver gives the same stationary placement for the equal-range example. The reduction justifies that solver even against pre-report motion.

## Source and replay

The [pinned 3D initial positions](https://github.com/KTH-DHSG/constrained_omrs/blob/cb87f91aaaa4e652de043704ce4dfb989e10bcde/src/constrained_omrs/scenario.py) come from the [open-team formation study](https://arxiv.org/html/2609.29939v1), whose manager builds a bridge before authorizing a connectivity-critical departure. This experiment uses the initial positions, not the manager or recorded outcomes. Selection and modeled link rules are in [FREEZE.txt](FREEZE.txt); the acceleration and speed are authored. The [classical enclosing-ball baseline](https://doi.org/10.1007/BFB0038202) is geometric, not a controller comparison.

With the pinned source saved as scenario.py:

    python3 replay.py scenario.py > actual.json
    diff -u results.json actual.json

The script checks the blob hash before parsing source literals. Certificates and the pass/fail decisions are exact rational calculations. The reported decimals are for reading. This extends the [two-world calculation](../notice-deadline/README.md). It does not cover collision constraints or moving recipients, measure packet reliability, or establish full R6.

The [inherited-state result](inherited-corridor/README.md) gives the exact endpoint check in a fixed scalar corridor and shows when requiring rest at the notice would wrongly reject a feasible mission.

The [joint formation result](formation-report-deadline/README.md) handles multiple moving robots and persistent clearance and link constraints. A cycle across three terminal requirements gives the exact report deadline.
