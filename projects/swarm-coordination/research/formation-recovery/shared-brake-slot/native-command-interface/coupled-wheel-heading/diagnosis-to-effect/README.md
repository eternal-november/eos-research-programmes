# Qualified receipt to a sampled differential-drive write

Use the full archive, or rehydrate the exact files in INPUTS.tsv and the four Gazebo pins in replay.py. Dependencies: Python 3, Git, g++ C++17. The replay links separate broker and drive objects into one serial timeline.

```sh
set -e -o pipefail
python3 -B replay.py | cmp - NATIVE.txt
python3 -B compare.py | cmp - RESULT.json
```

Each line gives cap, prior-charge age in eighths, alternate issuer, arrival phase (before step-two calculation, after it, after step-three calculation), source mode (current, old scope, erased), arc allowance, fault state, raw callback value, first usable step, charged diagnosis bytes, scaled arc length, and scaled final heading. -1 denotes absent. Receipt and physical tracking are not equated.
