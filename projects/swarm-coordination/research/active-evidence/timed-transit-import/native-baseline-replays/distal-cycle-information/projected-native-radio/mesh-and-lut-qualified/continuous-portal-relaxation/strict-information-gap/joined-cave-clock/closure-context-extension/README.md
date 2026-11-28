# Transport the cave route grant across four closure contexts

The geometric gate binding and timed trajectories are pinned to PR 878.
Requires the official cave data and native broker files under `up`
(Space 666) and included `base` and `parent`. Use Python 3 with NumPy
and a C++17 compiler.

```sh
bash replay.sh up parent base | cmp - EXPECTED.txt
```

This replays ray acquisition and route authorization, not the later dock
crash. The gates remain fixed from reading through egress. Both closed
means inspection is impossible in the declared authorized domain.
Different fresh hypotheses are needed for a moving gate or different
sensor or path family.
