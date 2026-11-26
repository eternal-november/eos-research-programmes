# Scoped world split at the physics setter

Use the pinned files in the parent Gazebo consumption and dual-writer
studies. Run from this directory:

```sh
python3 -B replay.py /path/to/pins
```

Source-body replay with declared write permissions and an authored positive
control. Both pose modes are modeled, not measured.

[Model and evidence](World_Rights_And_Local_Slots.tex). For a checked run
use `set -o pipefail` and pipe through `cmp results.txt -`.
