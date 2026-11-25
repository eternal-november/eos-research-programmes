# Paired reservation releases

[Statement and proof](Release_Order.tex). The same two released destinations and the same wait queue authorize one move or an arbitrarily long chain. A delayed promotion retains its waiting reservation, which is the next robot's destination.

Place the exact [pinned reservation node source](https://raw.githubusercontent.com/open-rmf/rmf_ros2/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_reservation_node/src/main.cpp) in this directory as `ReservationNode.cpp`. The replay verifies its Git blob digest; Python 3 and C++17 are required. Run `python3 replay.py | cmp replay.txt -`.

Only selected allocation code runs. The replay counts native destination grants in two delivered release orders; it does not establish actual motion, certify waiter clearance or change the deployed allocator.
