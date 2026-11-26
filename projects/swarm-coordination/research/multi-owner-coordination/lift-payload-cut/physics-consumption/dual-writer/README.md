# Shared component producer order

Build input for selected Gazebo 9 and Open-RMF replay; authorities and the
scope of each writer are not established by these source bodies.

Use the four pins from the [parent replay](../README.md), plus these exact
files from Gazebo at commit 62f198e0478159549b748c4b4c66f0cbe2fcbf6f:

- `VelocityControl.cc` from `src/systems/velocity_control/VelocityControl.cc`
- `ECM-detail.hh` from `include/gz/sim/detail/EntityComponentManager.hh`
- `SimulationRunner.cc` from `src/SimulationRunner.cc`
- `SystemManager.cc` from `src/SystemManager.cc`

```sh
python3 -B replay.py /path/to/pins
```

Use `set -o pipefail` and pipe the command through `cmp results.txt -`
to check the stored trace. An extracted helper and the selected linear
writer expression are executed; scheduler and priority configuration
are inspected, not run. See [evidence and limits](Producer_Order.tex).
