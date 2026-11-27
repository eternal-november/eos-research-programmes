#!/bin/sh
set -eu
cd "$(dirname "$0")"
UP=$(CDPATH= cd -- "${1:-inputs}" && pwd)
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
    test "$(git hash-object "$UP/$dest")" = "$sha"
done < SOURCE.tsv
export PYTHONPATH="$UP" OPENBLAS_NUM_THREADS=1
python3 -B trace_queries.py "$UP" > trace.json
cmp trace.json expected-trace.json
python3 -B overlap.py "$UP"
