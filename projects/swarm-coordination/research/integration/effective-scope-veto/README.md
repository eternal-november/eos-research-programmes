# Which command a lock can veto

[Statement, checked source, and supervisor comparison](What_A_Lock_Can_Veto.tex). A single priority threshold can express only nested exact isolated allow sets under fixed priorities. A diagnostic value is not an effective veto or a physical stop.

Run `python3 -B replay.py | cmp replay.txt -` with Python 3 and C++17, placing [topic_handle.hpp](https://github.com/ros-teleop/twist_mux/blob/a8225e2d9bf0171aac447c246376f0981defd17b/include/twist_mux/topic_handle.hpp) and [twist_mux.cpp](https://github.com/ros-teleop/twist_mux/blob/a8225e2d9bf0171aac447c246376f0981defd17b/src/twist_mux.cpp) here under the same basenames. The replay verifies blob digests; both input files are in the Space archive. Lean 4.35.0 with Mathlib verifies the abstract nesting consequences, not the C++ runtime. This does not run ROS or a robot.
