# A shared wind does not give independent demands

Run with the pinned
[WindEffects.cc](https://github.com/gazebosim/gz-sim/blob/62f198e0478159549b748c4b4c66f0cbe2fcbf6f/src/systems/wind_effects/WindEffects.cc):

```sh
python3 -B replay.py /path/to/WindEffects.cc
```

Only a selected source force callback and authored component state; no
dynamics, meteorology, sensor qualification, or hardware.

[Source comparison and exact modeled bound](Common_Exposure_And_Reserve.tex).
For the stored trace use `set -o pipefail` and pipe the result through
`cmp results.txt -`.
