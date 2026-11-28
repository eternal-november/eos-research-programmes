# Narrow delegation and shared-resource disclosure

Rehydrate INPUTS.tsv or use the exact full archive. Dependencies: Git, Python 3, C++17, libsqlite3.so.0.
```sh
set -e -o pipefail
bash replay.sh > NATIVE.txt
sha256sum -c NATIVE.sha256
python3 -B compare.py | cmp - RESULT.json
```
Each row: shared resource mask (bit 0 TX, bit 1 RX), split mask in the same bits, cap, public lag in eighths, shaping mode (none / positive only / padded), whether alternate issuer was lawfully delegated, whether authority rotated after receipt, private bit, SQLite permit, delivered private bit, actual unrelated acknowledgment, and qualified application use. Missing private values are -1. Counts apply only to this configuration grid.
