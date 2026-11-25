# ARIAC quality-service source calibration

Read [the calibration](ARIAC_Cached_Quality_And_Resumption.tex).

Obtain `ariac_plugins/src/task_manager_plugin.cpp` from the NIST ARIAC
commit `ffc825757dc05cc6e4dfbd5c2483e993aab35652`. The extractor checks
its full Git blob hash. It compiles three original functions with mocks
for the Gazebo and ROS dependencies; no simulator installation is used.

```sh
set -e -o pipefail
python -B extract.py /path/to/task_manager_plugin.cpp > upstream_extract.inc
g++ -std=c++17 -O0 harness.cpp -o run
./run | cmp result.txt -
```

Columns are trace name, valid ID, overall quadrant pass, incorrect tray,
and first quadrant faulty flag. The simulator source is not vendored.
