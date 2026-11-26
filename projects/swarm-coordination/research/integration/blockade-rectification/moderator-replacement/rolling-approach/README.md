# Approach a potentially occupied crossing without committing to enter

In the [continuous model](Rolling_Approach_At_A_Clearance_Cut.tex), a rolling approach beats waiting at the stop line. At the decision, the robot can still brake to the line if clearance is missing, or finish earlier if the crossing is physically clear. The proof optimizes over all admissible shared prefixes, not just stop and go policies.

The [native RMF check](../README.md) separates permission from actual exit. This follow-up explicitly assumes an accurate physical clearance report, uses an authored civil geometry, and extends the [inherited-state calculation](../../../../formation-recovery/managed-bridge-crash/standby-relay/joint-deadline/inherited-corridor/README.md). It does not establish that RMF supplies the report. The direct kinematic comparator has the same information and may use the same motion.

With Python 3 and SciPy:

    python3 replay.py > actual.json
    diff -u results.json actual.json
