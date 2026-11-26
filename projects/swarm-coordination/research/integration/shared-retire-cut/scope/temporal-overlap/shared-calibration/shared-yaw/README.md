# Shared yaw and timed occupancy

[Proof and scope](Shared_Yaw_And_Unbounded_Conflict_Rank.tex).
A bounded planar translation alone makes triples sufficient for the
geometric compatibility question. An uncertain shared yaw does not:
a narrow fixed yaw interval and one convex cell admit arbitrarily large
minimal conflicts.

Replay from this directory, retaining both enclosing replay modules:

```sh
python3 replay.py | cmp results.json -
```

The fixture uses Python's standard library, exact rational and quadratic
arithmetic, and the parent timing model. It tests the geometric algorithm
against a translation-elimination oracle and keeps isolated yaw directions.
No navigation source, physical clearance measurement, or mission acceptance
is claimed by this model.
