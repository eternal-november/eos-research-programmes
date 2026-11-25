# Protect unresolved shelves on return routes

[Result](Result.tex) · [Pre-execution freeze](FREEZE.txt). Both planner arms use the same guard, inputs and native MRWS effects. The guard changes only home-bound route search. It cannot undo a stop during installation or pickup and does not replace notice where a commissioned duty still needs a new supplier.

From the exact MRWS checkout used by the parent study, run the notice replay first. Use absolute paths from the local clone of this research project, with `base` for the blocked-source study, `notices` for its notice-timing subdirectory and `here` for this directory. Put `raw.json` in a writable output directory.

```sh
PYTHONHASHSEED=0 PYTHONPATH=simu python "$notices/with_notices.py" "$base/replay.py" /tmp/notices.json
PYTHONHASHSEED=0 PYTHONPATH=simu python "$here/shield.py" "$base/replay.py" /tmp/notices.json /tmp/raw.json
python "$here/check_shield.py" /tmp/raw.json /tmp/notices.json
sha256sum /tmp/raw.json
```

The raw trace must match `raw.sha256`. The backup contains the exact simulator files, both trace sets and the checked replay. Counts concern an authored deterministic development family, not independent validation.
