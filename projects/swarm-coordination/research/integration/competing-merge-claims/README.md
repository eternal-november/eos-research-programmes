# A competing merge claim changes the handoff

[Result and scope](Merge_Arbitration_Changes_The_Handoff.tex) · [declared test boundary](FREEZE.txt).

Use the exact inputs from [the native receipt replay](../native-handoff-receipts/README.md). Run the following with NumPy installed:

```sh
PYTHONHASHSEED=0 python3 -B arbiter_replay.py /path/to/pinned/sources > /tmp/merge-arbiter-raw.json
sha256sum /tmp/merge-arbiter-raw.json
```

The expected raw digest and example results are in `results.json`. The Space archive includes exact sources and standalone harnesses. The RWARE shim rejects tied maxima for the newly contested case.
