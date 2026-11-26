# Capability at an accepted lift session

Serial join of the original lift-session replay and the selected Gazebo 9
model consumer. Uses authored per-payload feature and entity state.
This is not hardware, mission completion, or failure of an observed fleet.

From this directory run:

```sh
python3 -B replay.py /path/to/pins
```

Use `Node.cpp`, `EndLiftSession.cpp` and `lift.cpp` from the parent
lift study and `Physics9.cc` from the physics-consumption study.

[Joined evidence and limits](Role_Entry_And_Recipient_Capability.tex).
For an exact comparison use `set -o pipefail` and pipe through
`cmp results.txt -`.
