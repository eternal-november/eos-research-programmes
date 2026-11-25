# Simultaneous delivery-port handoff

[Proof and limits](Simultaneous_Port_Handoff.tex) · [pre-execution scope](FREEZE.txt). This headless replay executes selected pinned warehouse methods. It extends the earlier one-mover harness only for functional graphs with injective nonstationary targets and explicit prefiltering. It does not model continuously safe robot motion.

Fetch `native_source.py` using the pin in [the source-and-return study](../rware-source-and-return/README.md). NumPy is required. Run:

```sh
PYTHONHASHSEED=0 python3 -B check.py /directory/with/native_source.py | cmp - results.json
```

Lean 4.35.0 with Mathlib checks the abstract dependency-closure lemmas. The Space archive includes the pinned source, harness and replay inputs.
