# MRWS guarded waiting and replanning

[Fixed protocol and findings](MRWS_Block_And_Replan_Development.tex). From a separate verified MRWS checkout at [941338e9](https://github.com/automaticdai/MRWS_MultiRobot_Warehouse_Scheduling/tree/941338e9ea4c4eaebb87f8374f80fd576497ad01), run:

```sh
PYTHONHASHSEED=0 PYTHONPATH=/path/to/MRWS/simu python3 -B matched.py /path/to/MRWS/simu/data/whouse7x11.txt rows.json | diff -u replay.txt -
sha256sum rows.json
```

Uses the local calibration module only to import the pinned native simulator without an optional genetic-scheduler dependency. The complete compared event summaries and digest are supplied with the replay.
