#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
    test "$(git hash-object "$UP/$dest")" = "$sha"
done < "$HERE/SOURCE.tsv"
export PYTHONPATH="$UP" OPENBLAS_NUM_THREADS=1
python3 -B "$HERE/model.py"
python3 -B "$HERE/verify_value.py"
python3 -B "$HERE/warmed_sql.py" "$UP"
