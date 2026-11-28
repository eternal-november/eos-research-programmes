# Cave report-to-egress and gate lease

Run `python3 mission.py` and `python3 lease.py` in the complete pinned
offline bundle. It needs Python 3, NumPy, SQLite, Git and C++17.
The last command reruns the native mission receive path before
computing the required lease. Both tools take `--geom`, `--source`
and `--paths` from a checkout. The two former directories are the
parent #803 artifact inputs; the path directory supplies the pinned
`near.json` and `far_short.json` from #788.

The comparison covers the declared synthetic gate and stationary-body
envelope, not the independent I2 mission.
