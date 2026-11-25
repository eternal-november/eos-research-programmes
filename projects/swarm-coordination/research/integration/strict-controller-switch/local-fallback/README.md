# Local controller fallback while a switch is outstanding

[Proof, five replay cases and scope](Local_Fallback_Before_Switch_Return.tex).

The manager's shared switch service can wait while its own update or
hardware-read path acts. The selected native slices also show when an
older switch skips a controller's error observation, when a fallback
takes a healthy controller's interface, and why a lifecycle transition
does not prove that the hardware accepted the change.

Supply the two source files from the pinned commit in [SOURCE.tsv](SOURCE.tsv)
under their original basenames. The replay verifies their blob IDs.

    sh replay.sh /path/to/upstream | cmp results.txt -

Requires Python 3 and a C++17 compiler. The service wait and device
effects are controlled stubs. This is not an ARIAC or a live ROS replay.
Lean checks only the declared-scope criterion.
