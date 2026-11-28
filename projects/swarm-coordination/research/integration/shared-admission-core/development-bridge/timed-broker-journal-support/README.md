# Timed common-history support for a broker and durable receipt

The standalone archive contains all pinned source files and the exact prior generator. For Git reconstruction, materialize INPUTS.tsv and copy event_support.py from [#839](https://github.com/eternal-november/eos-research-programmes/pull/839) beside support.py as prior_event_support.py; its blob is checked at import. Dependencies: Git, Python 3, C++17 compiler, Linux libsqlite3.so.0.

```sh
set -e -o pipefail
bash replay.sh > NATIVE.txt
sha256sum -c NATIVE.sha256
python3 -B support.py NATIVE.txt | cmp - RESULT.json
```

Each trace row gives cap, spacing in sixteenths of a second, dock probe policy (always / settled only / absent), result variant and event word. Per-cut digits encode committed row, probe observed (none/negative/positive), request arrival, exact returned value (none/SIDE/TIDE), and live bytes for original TX, dock RX, dock TX, collector RX and collector TX. Evaluator data is not given to the controller.
