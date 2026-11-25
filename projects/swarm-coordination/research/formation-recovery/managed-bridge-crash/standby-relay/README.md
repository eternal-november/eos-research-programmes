# A fixed standby for four abrupt departure cuts

[Proof, source scope and limitations](Standby_Relay.tex). Replays the two default point-mass formations in the same mode as [the previous calibration](../REPLAY.md). The failure scenarios are distinct counterfactual cuts on the original runs.

Populate the inputs listed in [PINNED.tsv](PINNED.tsv) from the [pinned author repository](https://github.com/KTH-DHSG/constrained_omrs/tree/cb87f91aaaa4e652de043704ce4dfb989e10bcde), with their paths relative to the `upstream/` subdirectory. Tested with Python 3 and NumPy 2.3.5.

```sh
set -o pipefail
PYTHONPATH=upstream/src python3 -B standby.py | cmp REPLAY.txt -
lean StandbyBounds.lean
```

Rational bounds and clearance assertions are the checked verdicts. The intermediate printed floats are the calibration outputs on the pinned replay.
