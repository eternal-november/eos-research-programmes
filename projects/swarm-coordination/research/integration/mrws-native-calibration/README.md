# Native MRWS fault source audit

[Scope and findings](MRWS_Native_Fault_Source_Audit.tex). Source: the public [MRWS commit](https://github.com/automaticdai/MRWS_MultiRobot_Warehouse_Scheduling/tree/941338e9ea4c4eaebb87f8374f80fd576497ad01). This is a source-qualification campaign with no held-out evaluation.

With a separate checked-out copy at that commit, run:

```sh
PYTHONHASHSEED=0 PYTHONPATH=/path/to/MRWS/simu python3 -B native_calibration.py /path/to/MRWS/simu/data science.jsonl | diff -u replay.txt -
sha256sum science.jsonl
```

The original log digest is recorded in `source-and-log.sha256`. The upstream source is not redistributed here. The development archive includes the native event log and full verification-only end-of-step state.
