# Door status and retained command effect

In this folder, extract and run the selected C++20 methods:

```sh
python3 door_effect.py door.cpp DoorOpen.cpp SupervisorHasSession.cpp utils.hpp > actual.txt
diff -u REPLAY_EFFECT.txt actual.txt
```

Use these exact upstream snapshots (copies also accompany the offline evidence):

- [door.cpp](https://github.com/open-rmf/rmf_simulation/blob/52b2478e41a92d3457155e4a1128d14437930f2c/rmf_building_sim_gz_plugins/src/door.cpp) and [utils.hpp](https://github.com/open-rmf/rmf_simulation/blob/52b2478e41a92d3457155e4a1128d14437930f2c/rmf_building_sim_gz_plugins/include/rmf_building_sim_gz_plugins/utils.hpp)
- [DoorOpen.cpp](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/phases/DoorOpen.cpp) and [SupervisorHasSession.cpp](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/phases/SupervisorHasSession.cpp)

The upstream command writer has an unused local `model`; its compiler warning is expected. The last three lines report native command and phase checks. The first line reports a separate, explicitly stipulated kinematic continuation. Neither runs actual ROS or physics. `Door_Effect.lean` checks the discrete decay and accumulated bound, not the source translation or door plant.
