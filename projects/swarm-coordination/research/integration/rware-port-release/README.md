# Port release before the old return

[Scope and findings](Native_Port_Release_Before_Return.tex) · [pre-execution boundary](FREEZE.txt). The two-stage credit and shelf movement use unmodified selected RWARE methods. The shared one-operation budget and old movement reservations are modeled inputs.

Retrieve the exact source matching the Git blob pin in [the source-and-return instructions](../rware-source-and-return/README.md); this replay does not use the separate published labels. Run:

```sh
PYTHONHASHSEED=0 python3 -B test.py /directory/with/native_source.py /tmp/native-drain.json
sha256sum /tmp/native-drain.json
```

The trace digest is in `results.sha256`. The backup includes the raw trace, native source and exact headless harness. No contract acceptance or change.
