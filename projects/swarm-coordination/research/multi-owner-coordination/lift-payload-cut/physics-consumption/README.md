# Lift write versus physics consumption and retirement

Serial selected-body replay. Download the following pinned files to one
directory with these names:

- `lift.cpp`: [Open-RMF simulator lift](https://github.com/open-rmf/rmf_simulation/blob/52b2478e41a92d3457155e4a1128d14437930f2c/rmf_building_sim_gz_plugins/src/lift.cpp)
- `Physics8.cc`: [Gazebo v8 physics pin](https://github.com/gazebosim/gz-sim/blob/d01b5c42944fa303ba547d0f1edfbda13f0dd725/src/systems/physics/Physics.cc)
- `Physics9.cc`: [Gazebo v9 physics pin](https://github.com/gazebosim/gz-sim/blob/62f198e0478159549b748c4b4c66f0cbe2fcbf6f/src/systems/physics/Physics.cc)
- `EntityComponentManager.cc`: [Gazebo v9 component manager pin](https://github.com/gazebosim/gz-sim/blob/62f198e0478159549b748c4b4c66f0cbe2fcbf6f/src/EntityComponentManager.cc)

```sh
python3 -B replay.py /path/to/pins
```

The fixture does not instantiate Gazebo, its step scheduler, or a physical
engine. It gives no hardware, actual motion, or compatibility certification.

For the checked trace run:

```sh
set -o pipefail
python3 -B replay.py /path/to/pins | cmp results.txt -
```

[Evidence and limits](Physics_Consumption_Cut.tex). The fixture executes
the selected lift write, physics setter dispatch, and cleanup bodies. The
component manager implementation and outer physics update order are
inspected, not run.

[Dual writer follow-up](dual-writer/): replacing the removed component can restore or overwrite the next lift intent depending on the order of the writers.

[Scoped frame quotient](frame-quotient/): one correct aggregate vector can conceal incompatible separately attributed world effects.
