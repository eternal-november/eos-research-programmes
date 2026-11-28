# Optional heading across a released navigation anchor

The standalone archive contains the exact pinned source bytes. For Git reconstruction, put the nine SOURCE.tsv files in pinned/ under their listed names. Dependencies: Python 3 and g++ C++20.

```sh
set -e -o pipefail
python3 -B replay.py | cmp - NATIVE.txt
python3 -B compare.py | cmp - RESULT.json
```

Each row identifies the phase (unreleased / released before dispatch / in flight), update form (replace from A / append from B), old and proposed heading codes (absent, 0, 1, positive pi, negative pi), acceptance, actual B heading, B callback version, and any subsequent C heading. The motion check is not a physical VDA run.
