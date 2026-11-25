# Native MRWS: fault notice timing is a separate intervention

[Model and findings](Notice_Timing_And_Recovery_Authority.tex) · [Pre-execution freeze](FREEZE.txt). This applies a notice shim to the exact [blocked-source development wrapper](../). It keeps the actual stop and shelf occupancy independent of whether its notice reaches the scheduler.

Use the source checkout and manifest described in the parent study. From the pinned MRWS root, set `base` to the parent study directory and `here` to this subdirectory, both absolute:

```sh
(cd simu && sha256sum -c "$base/source.sha256")
PYTHONHASHSEED=0 PYTHONPATH=simu python "$base/replay.py" /tmp/reference.json off-shelf
PYTHONHASHSEED=0 PYTHONPATH=simu python "$here/with_notices.py" "$base/replay.py" /tmp/notices.json
python "$here/check.py" /tmp/notices.json /tmp/reference.json "$base/expected.sha256"
sha256sum /tmp/notices.json
```

The result must match `raw.sha256`. The Space archive contains the full raw and reference traces and the exact source snapshot. In the model, motion and native inventory effects use the physical battery and cell state; only the scheduling call substitutes delivered fault status. This is not a production adapter or an independent validation.
