# Differential-drive braking and terminal heading

The complete archive contains the four hash-pinned Gazebo source inputs. For Git, native_replay.py lists exact repositories, revisions, paths and blob hashes. Dependencies: Python 3, g++ C++17. No whole Gazebo build is used.

```sh
set -e -o pipefail
python3 -B derive.py | cmp - EXPECTED.json
python3 -B derive.py --rows | cmp - ROWS.txt
python3 -B native_replay.py < ROWS.txt | cmp - NATIVE.txt
```

ROWS.txt has eight native positive profiles: fault state, notice step, then five left/right speed pairs. The proof establishes why no choices in the declared model reach the omitted late cuts. Lean 4.36 checks the cut arithmetic in WheelStop.lean. Source writes and modeled physical tracking are separate.
