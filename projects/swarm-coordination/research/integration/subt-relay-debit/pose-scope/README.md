# Pose readiness and receive capacity in a moving-link window

The pinned broker waits for every registered member to return a pose,
even for a direct unicast that does not use that member. A cached old
pose can instead return with the newest global timestamp. Both effects
matter for using the [braking-link window](../../../formation-recovery/managed-bridge-crash/braking-dwell/README.md)
as a report opportunity. The direct path law is a fixture assumption.

[Source inference, matched cases and proof limits](Pose_Scope.tex).
A scope-aware version preserves disjoint work; a shared receiver
requires reserving its still-live old debit. The six actual shared
receiver runs discriminate that failure from missing pose.

Supply the inputs listed in [SOURCE.tsv](SOURCE.tsv) at the pinned
relative paths. Then run (Git, C++17 and Python 3):

    sh replay.sh /path/to/inputs | cmp expected.txt -

Known blocked-source messages may be printed to stderr. The replay
does not deploy a broker or run the motion simulator as an RF source.
