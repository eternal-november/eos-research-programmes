# Replacing the blockade moderator while a crossing remains occupied

The native Open-RMF blockade logic in this replay initially holds a crossing and admits unrelated work. A fresh moderator accepts the crossing request before the previous route arrives. Re-registering that route does not restore its progress, and the next rectification cannot record the reached checkpoint under the new assignment. In a separate control the old robot's modeled location stays fixed while the previous grant changes; that alone changes the original moderator's answer.

The [note](Blockade_Across_Moderator_Replacement.tex) separates the native result from the physical fixture. Replaying the durable native prefix before accepting new requests holds the crossing without pausing disjoint work. The source grants an approach upon the old participant's readiness to leave, before actual modeled exit; a separate clearance rule is still needed for that service law.

## Replay

Check out [rmf_traffic at 4da6ff6](https://github.com/open-rmf/rmf_traffic/tree/4da6ff65e811038f73c6ca4e9ea3880a9af5938f) and [rmf_utils at 874e2f1](https://github.com/open-rmf/rmf_utils/tree/874e2f1ac84f727f18b3238a22aec411343f024e) under one parent using their repository names. The replay requires a C++17 compiler, Git, and an Eigen include root. It checks the 21 used source/header blob hashes in [SOURCE.tsv](SOURCE.tsv) before compilation.

    sh replay.sh /path/to/source-parent /path/to/eigen3 > actual.txt
    diff -u results.txt actual.txt

The fixture uses the native geometry and protocol classes in process. It does not connect to ROS, a transport, or a robot. See the earlier [selected-method test](../blockade-rectification/README.md) for the branch where the moderator explicitly reports a different reservation, rather than missing one.

The [rolling-approach model](rolling-approach/README.md) separates the modeled physical report from the native grant and gives the fastest conditional move that still allows a safe stop before clearance.
