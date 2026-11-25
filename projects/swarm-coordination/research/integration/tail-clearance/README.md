# Tail clearance and spacing interval finalization

[Source audit, exact recurrence and grant profile](Tail_Clearance_And_Completed_Intervals.tex). The source layer closes a simulated interval at its horizon, which can hide whether the tail actually reached the release boundary in that finite envelope. The geometric test keeps every input grant and isolated move duration fixed.

The replay takes six original Kotlin files from [OSRD's exact pin](https://github.com/OpenRailAssociation/osrd/tree/ccdd1b8ed80982f0e2e8a818d231f9dceffa0861). Use the basenames and SHA-1 Git blob digests listed in `replay.py`; the exact inputs are in the Space archive. Run `python3 -B replay.py | cmp replay.txt -`. Kotlin isn't executed. A separate [prior source replay](https://github.com/eternal-november/eos-research-programmes/pull/455) establishes the input grant trace. No ROS, railway operation, or real-time clearance is attempted here.
