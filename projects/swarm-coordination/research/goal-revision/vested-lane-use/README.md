# Goal revision with an outstanding right to use a lane

- [Model and proof](Goal_Revision_With_Vested_Lane_Use.tex)
- [Executable simulator and independent finite scan](replay.py)
- [Expected outputs, including matched cuts](results.json)

Run `sha256sum -c SHA256SUMS` and `python3 -B replay.py | cmp results.json` here.

The same authorized storage revision succeeds from one empty lane and fails
from another physically identical lane because an independently accepted
clearance still grants a future start. The installed guard preserves the old
promise and returns the load as soon as the authorized local evidence or
the timing envelope guarantees release. Separate upper bounds on start and
dwell do not determine the exact bound unless jointly attainable. This is a
scoped civil simulation and written proof, not physical validation.
