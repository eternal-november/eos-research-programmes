# Lift sessions and carried payloads

[Source-backed scope note](Lift_Session_And_Payload_Effect.tex).
The pinned simulator rejects a different request while its lift command
is active. After that command finishes, its next payload velocity write
depends on who is in the simulated cabin, not who owns the session.
The same reported session and commands can coexist with different writes.

Download these pinned files, using the basenames below:

- [Node.cpp](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/lift_supervisor/Node.cpp)
- [EndLiftSession.cpp](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/rmf_fleet_adapter/phases/EndLiftSession.cpp)
- [lift.cpp](https://github.com/open-rmf/rmf_simulation/blob/52b2478e41a92d3457155e4a1128d14437930f2c/rmf_building_sim_gz_plugins/src/lift.cpp)

Run with C++20 and Python 3:

```sh
python3 replay.py /path/to/pins | cmp results.txt -
```

The replay compiles selected unchanged bodies. Floor/door completion,
poses, and input cabin velocity are explicit in-process model inputs.
Only the command and payload write is observed; no ROS, Gazebo,
hardware, or physical clearance claim.

[Scoped effect windows](scoped-effect-window/): a separate jointly indexed authority model and exact issue-time calculation.
