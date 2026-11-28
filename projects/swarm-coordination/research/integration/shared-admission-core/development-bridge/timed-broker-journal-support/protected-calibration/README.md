# Protected report diagnostics and original-cut identification

Rehydrate INPUTS.tsv or use the complete Space archive. Dependencies: Python 3, Git, g++ with C++17, libsqlite3.so.0.
```sh
set -e -o pipefail
bash replay.sh | cmp - NATIVE.txt
python3 -B identification.py | cmp - RESULT.json
```

Per row: U, V, staging action, exact payload variant, arm, late-copy timestamp times eight, number of delivered requests, exact reply code, audit bit at collector Q, audit bit at separate endpoint T, original-cut reply code in the fallback arms, and actual charged payload bytes from time 2 onward. Arms 0–8 are tight; protected only; protected with shared historical audit; protected with separate historical audit; protected with separate current-fit audit; separate wrong-dock historical audit; isolated dock-0 timestamp-only; same sender retry; authorized separate sender retry. An absent tag is -1. Evaluator columns are not assumed to be observed in the baseline histories.
