# An empty edge report does not rule out a pending move

Two hypothetical route updates give the same published route fields in the pinned ROS-Industrial adapter, but the navigation callback receives different incoming edges. The difference is the first edge of the update. It is absent from the state manager's edge array and present in the active route used by the callback. The replay controls for both initial orders, which report the first edge, and unreleased updates, which do not dispatch.

The [note](Edge_Absent_Not_Clear.tex) describes the boundary. An observer that has retained the actual accepted payload can recover the edge identity; the selected status fields alone cannot. No physical occupancy or clearance is inferred.

## Replay

Use C++20 and Python 3. Save these four pinned files under their original basenames:

- [order_graph_validator.cpp](https://github.com/ros-industrial/vda5050_core/blob/a81ff9d600e8e30a35af25c152a3445c29c12f5f/vda5050_core/src/validation/order_graph_validator.cpp)
- [state_manager.cpp](https://github.com/ros-industrial/vda5050_core/blob/a81ff9d600e8e30a35af25c152a3445c29c12f5f/vda5050_core/src/client/adapter/state_manager.cpp)
- [adapter.cpp](https://github.com/ros-industrial/vda5050_core/blob/a81ff9d600e8e30a35af25c152a3445c29c12f5f/vda5050_core/src/client/adapter/adapter.cpp)
- [edge_request.cpp](https://github.com/ros-industrial/vda5050_core/blob/a81ff9d600e8e30a35af25c152a3445c29c12f5f/vda5050_core/src/client/adapter/edge_request.cpp)

Then run:

    python3 replay.py order_graph_validator.cpp state_manager.cpp adapter.cpp edge_request.cpp > actual.txt
    diff -u results.txt actual.txt

Hashes are checked before compiling. The accepted route-update boundary is described in the [parent validation replay](../README.md). This follow-up is a serial, selected-code check with inert types and no fleet or MQTT connection.
