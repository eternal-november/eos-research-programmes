# Shared frame uncertainty through a monitor's consecutive counters

[Exact relation and proof](Same_Error_Through_Hysteresis.tex).
Two frames can each cause a possible hit without sharing any uncertainty
realization that produces both. The analogous construction also prevents
a release based on consecutive misses. A bounded change to the shared
shift gives sharp, strict thresholds in the two cases.

Download these files from the
[pinned Navigation2 tree](https://github.com/ros-navigation/navigation2/tree/346bd05f40b62ae60b96ba86e02eb491c8dba444)
to one directory under their original names:

- `nav2_collision_monitor/src/polygon.cpp`
- `nav2_util/include/nav2_util/geometry_utils.hpp`

```sh
python3 replay.py /path/to/pins | cmp results.json -
```

The replay compiles selected unchanged native polygon code for a fixed
rectangle and separately verifies a rational uncertainty relation under
assumed shared shifts. It does not run the monitor node or test physical
clearance, sensing quality, real TF behavior or robot braking.

[Acquisition and use cuts](scan-use/): native counters count monitor evaluations, not distinct acquisitions, and a repeated scan can still give a different current projection.

[One correction across two-stamp uses](one-correction-timeline/): preserve a single correction history through both counters; adjacent and overlapping stamp windows differ.
