# Motor-current acquisition versus publication

[Source boundary and exact freshness bound](A_Published_Current_Can_Be_Stale.tex) · [recorded scope](FREEZE.txt).

Download the exact pinned `force_control.py` linked in the note, then run with NumPy 2.3.5:

```sh
PYTHONHASHSEED=0 python3 -B replay.py /path/to/force_control.py | cmp - results.json
```

The fixture executes unmodified selected methods and mocks ROS and electrical interfaces. An explicit scalar adapter isolates the sensor-failure test from the independent NumPy 2 indexing control.
