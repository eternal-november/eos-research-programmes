# Radio transport of a keyed motion result

Run the offline bundle with Python 3, NumPy, SQLite, Git and C++17:

    python3 -B journal_wire.py | cmp - REPLAY_WIRE_FINAL4.txt

From a repository checkout provide the original source files as in the
[selector fixture](../../../README.md), using `--source`, `--warehouse`,
and `--support`. The keyed plant parent is discovered and pinned.

Each witness case is (settled-before-crash, B-blocked, keyed-transfer
mode, Q-cap, B-cap, gap, other-report-size, policy, scheduling order).
Transfer modes 0, 1, 2 are valid, missing, stale. Gap 0 is exactly
one second and 1 is 17/16. Order 0 requires the independent report
first and 1 permits it after the reply. Arms 0/1 are common and
direct; 2 does not guard the two capacity directions, and 3
treats missing keyed authorization as pending.
