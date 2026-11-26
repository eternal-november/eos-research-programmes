# Recalibration and an outstanding navigation request

[Proof and replay scope](Calibration_Capture_Cut.tex). A fresh pose does not say
which calibration was used to make an already-issued navigation target.
The unchanged selected VDA 5050 adapter bodies give two serial traces with the
same pose, order and current transform but distinct numeric callback targets.
The fixture stops at that callback. This concerns recalibration within one
physical gauge, not a claim about VDA 5050 map version activation.

## Replay

Download these seven files from
[the pinned ROS-Industrial tree](https://github.com/ros-industrial/vda5050_core/tree/a81ff9d600e8e30a35af25c152a3445c29c12f5f)
into one directory under their original basenames. The replay checks all Git
blob hashes before compiling.

- Under `vda5050_core/src/client/adapter/`: `adapter.cpp`, `state_manager.cpp`,
  `transformation.cpp`, `node_request.cpp`.
- Under `vda5050_core/include/vda5050_core/client/adapter/`: `transformation.hpp`,
  `node_request.hpp`.
- Under `vda5050_core/test/client/`: `test_adapter_navigation.cpp` (inspected,
  not executed).

```sh
python3 replay.py /path/to/pins > actual.txt
cmp results.txt actual.txt
```

The C++20 fixture supplies inert stand-ins for unrelated interfaces. The
callback receives the actual transformed request type and keeps it pending.
The proof compares with a direct planner retaining the same local target;
there is no claimed advantage over that baseline.

[Captured curve follow-up](captured-curve/): world trajectory versus converted node position in the callback, plus exact suffix revalidation in a separate corridor model.
