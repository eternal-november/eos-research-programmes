# Scan acquisition versus monitor evaluation

[Source replay and evidence contract](Scan_Acquisition_And_Use_Cuts.tex).
Two admitted evaluations can use the same acquisition, and its
projected membership can change as the base moves. The independent
corroboration example counts distinct clear acquisitions without
ignoring a hit at an intervening use of an old scan.

Download these files from the
[pinned Navigation2 tree](https://github.com/ros-navigation/navigation2/tree/346bd05f40b62ae60b96ba86e02eb491c8dba444)
to one directory under their original basenames:

- `nav2_collision_monitor/src/source.cpp`
- `nav2_collision_monitor/src/scan.cpp`
- `nav2_util/include/nav2_util/geometry_utils.hpp`
- `nav2_collision_monitor/src/polygon.cpp`
- `nav2_collision_monitor/src/collision_monitor_node.cpp`

```sh
python3 replay.py /path/to/pins | cmp results.txt -
python3 corroboration.py | cmp corroboration.json -
```

The fixture executes selected unchanged methods with a stand-in for
the full node process and a declared transform provider. The separate
authored evidence policy is not stock Navigation2 or a clearance
certificate.
