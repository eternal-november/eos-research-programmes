# An unpublished release and an unacknowledged release are different

A robot can retain work on the already released base while replacing an unreleased continuation. That does not make a sent-but-unacknowledged release revocable. The same newer update at an old anchor is accepted if it reaches the robot first and rejected if the earlier extension already reached it. The higher update number prevents late replay after acceptance; it does not remove an extension accepted before it.

The [proof and scope note](Released_Base_Cut.tex) separates this order-acceptance result from physical control. It uses the released-base rule in the [VDA 5050 specification, §6.6.2](https://www.vda.de/dam/jcr%3Af0c9c019-1506-4dee-998a-e92723fbf025/EN-VDA5050-V2_1_0_2025-01.pdf) and runs the unchanged body of the graph/update validator from the [pinned ROS-Industrial implementation](https://github.com/ros-industrial/vda5050_core/blob/a81ff9d600e8e30a35af25c152a3445c29c12f5f/vda5050_core/src/validation/order_graph_validator.cpp). This is a selected-module execution, not a live protocol run.

Save the pinned [validator](https://github.com/ros-industrial/vda5050_core/blob/a81ff9d600e8e30a35af25c152a3445c29c12f5f/vda5050_core/src/validation/order_graph_validator.cpp), [adapter](https://github.com/ros-industrial/vda5050_core/blob/a81ff9d600e8e30a35af25c152a3445c29c12f5f/vda5050_core/src/client/adapter/adapter.cpp), and [navigation test](https://github.com/ros-industrial/vda5050_core/blob/a81ff9d600e8e30a35af25c152a3445c29c12f5f/vda5050_core/test/client/test_adapter_navigation.cpp) under their original basenames. Then run:

    python3 replay.py order_graph_validator.cpp adapter.cpp test_adapter_navigation.cpp > actual.txt
    diff -u results.txt actual.txt

The harness requires a C++20 compiler. The adapter and its native test are pinned and inspected, not run in the harness. No MQTT, live fleet, driver, timing claim, or physical clearance certificate is involved.

The [first-edge follow-up](first-edge-report/README.md) executes the selected state and navigation methods and finds a released first edge that the callback receives but the report omits.
