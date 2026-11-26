# Jointly conditioning a pose and a remaining curve

[Exact bound and proof](One_Offset_For_Pose_And_Clearance.tex). In this scalar
model, a bounded pose observation constrains both curve progress and the
offset that can apply to the remaining curve. Keeping that dependence permits
a continuation that summing the exact separate peaks refuses. Allowing the
offset to drift gives an exact boundary for that reuse.

```sh
python3 replay.py | cmp results.json -
```

The replay imports the adjacent shared-yaw study's exact root-sign arithmetic
for a separate decision comparator. An explicit path to `phase.py` can be
supplied as the first argument when running the standalone backup.
No source is assumed to provide the modeled progress or pose witness.
