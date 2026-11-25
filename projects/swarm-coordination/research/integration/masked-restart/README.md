# Restart from masked fault labels

Source qualification for HSU TwinFlow and a timed benchmark for waiting on an old effect while revalidating a repaired component. The timing examples are authored, not TwinFlow held-out records.

- [Source scope, exact model and matched cases](Restart_From_Masked_Fault_Labels.tex)
- Run `python3 replay.py` for the standard-library timing replay.
- For the upstream transformation check, separately obtain [TwinFlow's preparation script](https://github.com/imb-hsu/twinflow/blob/d8c623bbf3866b6edef4ef3f3b160229fd5c46f4/scripts/prepare_data.py), with exact Git blob `6dde97dff447ee6f6d8fdb0e4c22423014a091b8`. Run `python3 replay.py path/to/prepare_data.py | diff -u replay.txt -` with Pandas. Only the pinned masking function is evaluated and only on fixture inputs.
- `RestartValidation.lean` checks the timing bounds and the sharp threshold on the extra delay of an isolated test.
