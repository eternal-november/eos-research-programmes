# Pooled diagnostics and context-dependent failure risk

[Statement and proof](Pooling_Can_Hide_Which_Repair_Is_Safe.tex) · [Scope freeze](FREEZE.txt). This uses the actual outcome table from the pinned MRWS return guard, with authored fixed scenario laws and recording modes. It is not a field estimate.

Recreate the guarded raw trace using [the parent source replay](../../integration/mrws-blocked-source/return-route-guard/README.md). The archive also includes that exact trace. Then run:

```sh
python3 -B replay.py /path/to/guarded-raw.json | cmp - results.json
```

The loader verifies the raw SHA-256 and checks that the two recovery choices match before their decision cut. Tests cover 729 binary-cell cases and 1,260 extremum queries checked against direct vertex enumeration. `Pooling.lean` checks the two-context sharp bound and optima bounds in Lean 4.35.0 with Mathlib.
