# Operator handoff and the retained interruption hold

Selected normal task interruption and release, with an independent co-hold.
The fixture does not take over a robot or invoke a deployed interface.

Use the following files from rmf_ros2 at
`16a3457196c6edf2f08a1ba4f497bf891404cbb7`:

- `TaskManager.cpp` under `rmf_fleet_adapter/src/rmf_fleet_adapter/`
- `RobotUpdateHandle.cpp` under `rmf_fleet_adapter/src/rmf_fleet_adapter/agv/`
- `RobotUpdateHandle.hpp` under `rmf_fleet_adapter/include/rmf_fleet_adapter/agv/`

```sh
python3 -B replay.py /path/to/pins
```

[Evidence and modeled handoff obligation](Operator_Handoff_At_Actuation.tex).
For an exact run use `set -o pipefail` and pipe to `cmp results.txt -`.

[Exclusive effect follow-up](exclusive-effect/): authored clock/qualified-release law, not inferred from task pause or ready events.
