# A moving relay at the observation cut

At the same corridor position, opposite velocities give disjoint sets of feasible terminal stops in the worked example. Requiring a stop at the observation cut is also too conservative: a shared moving prefix can reach either required terminal by time 4, while any policy at rest at the cut loses one case.

The [proof](Inherited_Corridor_State.tex) returns the exact interval of terminal stops from a measured position and velocity. First check the minimum braking excursion against the walls, then clip the unconstrained interval. This interval suffices for terminal queries at that deadline, not for new physical constraints.

Run the exact replay with Python 3:

    python3 replay.py > actual.json
    diff -u results.json actual.json

The independent lattice calculation checks the unrestricted extrema. Wall safety follows from the braking and monotone segment constructions. This is an authored example, not a test of a robot. It complements the [free standby result](../README.md) by fixing the inherited motion state instead of choosing a standby location.
