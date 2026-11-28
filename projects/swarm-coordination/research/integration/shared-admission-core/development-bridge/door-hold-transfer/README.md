# Development transfer to expiring door holds

Run from an unpacked Space bundle:
`set -o pipefail; python3 -B door_transfer.py | cmp - GATE_EXPECTED.json`.
C++20, Node and Python are needed. `sha256sum -c SHA256SUMS` checks the
archived copies. In a repository checkout use `--source`, `--template`,
`--extractor`, `--policy` and `--model` for the materialized inputs.
The latter two are pinned by the parent checker and this driver.
Read the TeX for the exact aperture, authorization and source limits.
