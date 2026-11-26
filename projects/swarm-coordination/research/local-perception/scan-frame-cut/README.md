# A fixed-frame correction between scan and use

[Proof and scope](Same_Gauge_Across_Age.tex). An age-valid delayed scan can
depend on a transform across two calibration epochs. A fixed common gauge
error cancels; a jump need not. A stable relative reference avoids that
particular error without discarding compensation for motion.

Download these files from the
[pinned Navigation2 tree](https://github.com/ros-navigation/navigation2/tree/346bd05f40b62ae60b96ba86e02eb491c8dba444)
to one directory under their original basenames:

- `nav2_collision_monitor/src/source.cpp`
- `nav2_collision_monitor/src/scan.cpp`
- `nav2_ros_common/include/nav2_ros_common/tf_manager.hpp`

```sh
python3 replay.py /path/to/pins | cmp results.txt -
```

The selected methods run unchanged with serial stand-ins. The manager's
delegation to TF is inspected, not native TF buffer execution. No actual
vehicle, hazard or braking claim.
