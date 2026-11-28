# Door request lifetime and scope

Run the archived fixture using Python 3 and C++20:

    python3 -B replay.py | cmp - REPLAY.txt

The replay extracts exact upstream method bodies from these pinned files;
name them as indicated by the script:

- [Supervisor.cc](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/door_supervisor/Node.cpp)
- [DoorClose.cc](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/phases/DoorClose.cpp)
- [RobotContext.cc](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/agv/RobotContext.cpp)
- `gate_receipt.hpp` from [#809](https://github.com/eternal-november/eos-research-programmes/pull/809/files)

For the separate caller/time audit, see the pinned
[adapter worker](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/agv/Adapter.cpp),
[transport dispatch](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/rmf_rxcpp/include/rmf_rxcpp/Transport.hpp),
[legacy phase shim](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/events/LegacyPhaseShim.cpp)
and [subscription guard](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/rmf_rxcpp/include/rmf_rxcpp/RxJobs.hpp).
The serial-retired and retained cases below that seam are intentionally
different lifetime fixtures. Neither executes the full ROS or task stack.
