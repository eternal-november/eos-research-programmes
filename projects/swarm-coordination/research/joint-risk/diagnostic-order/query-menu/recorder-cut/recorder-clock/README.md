# Decide the empirical cap without choosing a join

The [proof](Empirical_Risk_With_Shared_Clock.tex) bounds the union of the failure flags across complete paired episodes. A shared offset is kept in the matching problem, not separately minimized for each pair. In the replay, two cross-pairs are individually admissible at different offsets. Joining them falsely changes the observed failure count from one to two. In a separate case multiple assignments survive, but they all give the same count.

The clock constraint is analogous to the project’s [shared-clock custody check](https://github.com/eternal-november/eos-research-programmes/pull/395). The replay extends the [parent recorder check](../README.md), using its pinned recorder and writer header and the same C++ test seam. The [ROS Image message definition](https://github.com/ros2/common_interfaces/blob/832de8e0ff0d2116a92e936e723d4db4022a8e0c/sensor_msgs/msg/Image.msg) illustrates why acquisition stamps belong in the input contract. Here the stamp and failure flag are fixture payloads; this is not an Image driver or a calibrated clock experiment. The [ROS message-filter synchronizer](https://github.com/ros2/message_filters/blob/rolling/doc/index.rst#6-policybased-synchronizers) chooses timestamp-based matches; neither it nor the recorder guarantees this acquisition model. The exact optimizer uses [ordinary weighted assignment](https://doi.org/10.1002/nav.3800020109), checked against direct feasible-join enumeration.

From this directory, supply the directory with both pinned files from the parent SOURCE.tsv:

    sh replay.sh /path/to/upstream .. > actual.json
    diff -u results.json actual.json

The relevant information is the complete source-compatible matching family. The consumer is the monotone cap on this empirical sample, not arbitrary linkage, causal attribution, or population risk.
