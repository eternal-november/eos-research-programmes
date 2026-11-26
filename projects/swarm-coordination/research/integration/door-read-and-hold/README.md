# Check all expected leaves before trusting an open door report

The [source note](Door_Joints_And_Session_Cut.tex) composes the pinned simulator's joint lookup, mode calculation and publication with the pinned Open-RMF door-open predicate. A visible open leaf plus an unresolved second leaf can produce the same OPEN state as two observed open leaves. A matching supervisor session then completes the phase in both fixtures. A separate test pairs an older fully observed OPEN with a new session; their coexistence at the required time is not checked.

The replay executes the selected original methods with inert types. It does not spin ROS, Gazebo, or the reactive stream and it does not use a live door. A complete-sample guard is tested at the data source, not claimed to run on stock reports. Timestamp association and continued hold remain separate obligations.

Save these pinned files: [door.cpp](https://github.com/open-rmf/rmf_simulation/blob/52b2478e41a92d3457155e4a1128d14437930f2c/rmf_building_sim_gz_plugins/src/door.cpp), [DoorOpen.cpp](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/phases/DoorOpen.cpp), and [SupervisorHasSession.cpp](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/phases/SupervisorHasSession.cpp). With Python 3 and C++20:

    python3 replay.py door.cpp DoorOpen.cpp SupervisorHasSession.cpp > actual.txt
    diff -u results.txt actual.txt
