# Compound cave dock handoff, development replay

`python3 replay.py | cmp - REPLAY_NATIVE.txt` in the complete offline
bundle. It needs Python 3, NumPy, Git and a C++17 compiler. The build
only writes a temporary directory.

From a checkout, run `python3 replay.py --geom /path/to/parent-egress-material --source /path/to/parent-source-material`.
The geometry and source are the pinned materials of the [earlier cave replay](https://github.com/eternal-november/eos-research-programmes/pull/788).
The geometry also uses the already archived Straight 03 mesh at tile 18.
The source directory includes the exact Cave Circuit 01 visibility lookup.
The unchanged admission core is read by Git blob hash. Using another
copy requires the same blob, not a source-specific patched evaluator.

The phase, payload, declared envelope, comparisons and exclusions are
in the adjacent TeX. The figures are development-fixture counts and
not observations of deployed radios or mechanical safety.
