# MRWS: recovery with a blocked class source

[Result and scope](Result.tex). This study extends the [callback test](../mrws-retained-loads/) to executed warehouse ticks. Both recovery arms lose service if a stopped robot blocks the only source of a required class and no healthy actor holds that class. A separate control shows why recovery routing can determine whether the second failure creates that obstruction.

Clone [MRWS](https://github.com/automaticdai/MRWS_MultiRobot_Warehouse_Scheduling), check out `941338e9ea4c4eaebb87f8374f80fd576497ad01`, and run from its root, with the two scripts in this directory identified by absolute path:

```sh
(cd simu && sha256sum -c /path/to/this-directory/source.sha256)
PYTHONHASHSEED=0 PYTHONPATH=simu python /path/to/this-directory/replay.py /tmp/mrws-v1.json original
PYTHONHASHSEED=0 PYTHONPATH=simu python /path/to/this-directory/replay.py /tmp/mrws-v2.json off-shelf
python /path/to/this-directory/check.py /tmp/mrws-v1.json /tmp/mrws-v2.json
```

The source manifest lists only required inputs; genetic scheduling and the viewer are disabled. The archived independent trace checker covers cell occupancy, actual shelf pickups, ordered class settlement, movement budgets, and the blocked-source witnesses. Replay trace digests are in `expected.sha256`. The raw 224 traces and the two pre-execution intervention declarations are in the [Space backup](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80). This is a scoped developmental comparison with the native discard rule, not I1 acceptance.
