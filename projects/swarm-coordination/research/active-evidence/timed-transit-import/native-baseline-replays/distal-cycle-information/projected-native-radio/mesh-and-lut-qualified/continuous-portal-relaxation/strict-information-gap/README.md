# Exact continuous cave separation in the scoped center domain

Use the `up/` inputs from the mesh-and-LUT-qualified Space archive (#872).
Source model versions and their hashes are in ASSETS.tsv and COLLISION.sha256.
The replay certifies fixed paths and saved integer dual vectors; it does not
solve a numerical optimization problem during verification.

```sh
bash replay.sh /path/to/qualified/up | cmp - EXPECTED.jsonl
```

Python 3, NumPy and Git are required. Optional `discover_duals.py` uses SciPy
to propose replacement vector certificates; `positive_discovery.py` uses the
previous round-trip paths as seeds from an input JSONL. Neither generation
procedure is relied on for certificate soundness.
