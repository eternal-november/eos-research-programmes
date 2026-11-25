# RWARE source protection and the outstanding return

[Findings](RWARE_Source_And_Return_Proof.tex) · [Pre-execution intervention](FREEZE.txt).

To replay, place these exact files in one local source directory using the listed names. The loader verifies their Git blob hashes and extracts only the specified native and label methods.

- [RWARE warehouse.py](https://github.com/semitable/robotic-warehouse/blob/96fbc64e3eae5fee915e0d390f864fa06ddccd47/rware/warehouse.py), save as `native_source.py`, blob `9797bf36970d5eb14fef7a150fab7562c450dff6`.
- [Published contract-shielding RWARE labeller](https://github.com/nightly/contract-shielding/blob/07ef8d482325ce8450753cba0276511b81d26ec3/src/environments/rware/labelled/__init__.py), save as `published_labels.py`, blob `f8735c9e46a8a64981da126b7c1ac48237d6a651`.

```sh
PYTHONHASHSEED=0 python3 -B replay.py /path/to/sources /tmp/rware-trace.json
sha256sum /tmp/rware-trace.json
python3 -B check_trace.py /tmp/rware-trace.json
```

The known digest is in `trace.sha256`; the raw trace is in the [Space backup](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80). The replay requires NumPy and uses native methods on a scoped fixture, not the full Gym runtime. The protected-route policy does not replace the published contract synthesis procedure.
