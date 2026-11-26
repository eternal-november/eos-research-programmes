# Closure notice and corridor release

The paper describes what can be reused under a scoped closure, and what a civil
site coordinator needs before giving a shared corridor back to a maintenance crew.
The code is not a deployment patch. `replay.py` compiles exact selected bodies
from Open-RMF rmf_ros2 at `16a3457196c6edf2f08a1ba4f497bf891404cbb7`, wired
through authored schedulers, geometry and sink stubs. Copy these files from
that commit to a separate source directory before running the replay:

- `rmf_fleet_adapter/src/full_control/main.cpp` as `full_control.cpp`
- `rmf_fleet_adapter/src/rmf_fleet_adapter/agv/FleetUpdateHandle.cpp`
- `rmf_fleet_adapter/src/rmf_fleet_adapter/agv/RobotUpdateHandle.cpp`

From this directory, run `python3 -B replay.py /absolute/source/dir`.
Requires a C++20 compiler. The replay checks blob identities first. The worker is
explicitly drained after the request publication in the fixture. Real ROS
dispatch, physical brakes, body clearance, plan completion, and an actual
maintenance permission protocol are not replayed.

Run `python3 -B guard.py` for the separate timed effect model. Its outsider
exclusivity obligation is explicit, and a declaration of administrative closure
does not supply a physical fence. `Clear.lean` checks core monotonicity and the
late-entry counterhistory with Lean 4.35.0 + Mathlib.
