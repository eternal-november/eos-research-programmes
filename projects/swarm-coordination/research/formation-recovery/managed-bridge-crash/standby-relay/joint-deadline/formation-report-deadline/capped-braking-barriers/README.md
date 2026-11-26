# Braking margins with limited speed and a shared middle actuator

The [proof](Exact_Braking_Barriers.tex) gives two independent failure modes for a pairwise braking test. With independent speed caps, identical relative velocity need not imply identical clearance; the robot at the cap cannot supply the advertised acceleration. With three equally accelerated robots, even exact isolated pair margins do not establish a feasible shared maneuver. A tight outer-gap requirement gives the missing check in the stated family.

[Wang, Ames and Egerstedt's published compositional barriers](https://liwanggt.github.io/files/B5_Composable_Barrier.pdf), Section IV, provide the common-cap and composition comparator. The counterexample concerns transporting the pair formula to different caps and dropping its joint feasibility premise, not the source theorem's own claims. The examples also distinguish static gap at a cut from the ability to brake before a violation.

    python3 replay.py > actual.json
    diff -u results.json actual.json

This is a continuous forward-only safety law, not a guarantee of stopping at a mission target, communications or real robot behavior.

[Monotone-speed chains](monotone-chain/) extend the span test to arbitrary length when limits are common, and give the exact safe stop time.

[Directed position constraints](directed-constraints/) remove the monotone-velocity assumption through shortest-path closure and show where unequal actuators break the test.

[Delayed braking reports](report-delay/) give the exact clearance cost of a common blind prefix and show why the sum of two gaps can lose decisive information.

[Incremental constraint admission](constraint-amendment/) reuses an old safe-stop certificate and tests a small batch of changes without rechecking every robot pair.
