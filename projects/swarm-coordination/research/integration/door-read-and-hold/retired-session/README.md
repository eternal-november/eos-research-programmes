# A delayed open can recreate a closed session

The [source and proof note](Retiring_A_Door_Session.tex) checks the pinned door supervisor. The native log can reject a stale close while an active open remains, but forgets the closed requester's time when it removes that entry. In the replay, a delayed open restores the retired session and prevents a different holder from closing the door later. A retained terminal version distinguishes old attempts from new ones under the specified order law.

This is a message and command trace, not physical door motion. The [parent study](../README.md) checks the independent completeness and freshness of the door's OPEN report.

Save [the pinned Node.cpp](https://github.com/open-rmf/rmf_ros2/blob/16a3457196c6edf2f08a1ba4f497bf891404cbb7/rmf_fleet_adapter/src/door_supervisor/Node.cpp), then run with Python 3 and a C++20 compiler:

    python3 replay.py Node.cpp > actual.txt
    diff -u results.txt actual.txt
