# Health received during a switch

[Short proof and source scope](Callback_Cut.tex). This follows the
[parent](../README.md) calibration but tests the consumer with a correctly
delivered health change. It does not rely on the parent study's
class-wide health reset.

From this directory, using the same pinned switcher file as the parent:

    python3 -B callback_replay.py /path/to/robot_controller_switcher_node.py | cmp results.json -

The pinned switcher is executed unchanged, then with a two-placement
change to when its pending flag is consumed. The fixture controls the
order of ROS callbacks and the service outcome. A rejected switch still
needs a separate actual-state check.
