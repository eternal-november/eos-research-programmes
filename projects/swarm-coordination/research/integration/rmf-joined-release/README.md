# Joined zone idle and release-order replay

[Scope, proof, and interpretation](Joint_Release_Clock.tex). The exact selected Open-RMF zone release publisher feeds its actual ticket into the exact selected reservation node in the same replay. The analytic and executable physical guards are separate from the native grant.

Copy `Node.cpp` and `ZoneReservationClient.cpp` from the [pinned zone directory](https://github.com/open-rmf/rmf_ros2/tree/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/zone_manager) and the [reservation node source](https://raw.githubusercontent.com/open-rmf/rmf_ros2/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_reservation_node/src/main.cpp) as `ReservationNode.cpp`. Their blob hashes are checked, and the exact bytes are in the Space archive. Run `python3 -B replay.py | cmp replay.txt -` with Python 3 and C++17.

The release transport/chosen ticks, declared source setup, and integer-time physical effect model are controlled. This is not a deployed ROS run or a claim of independent field service.
