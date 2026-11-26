#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r sha name; do
    test "$(git hash-object "$UP/$name")" = "$sha"
done < "$HERE/PINNED.tsv"
PYTHONPATH="$UP/src" OPENBLAS_NUM_THREADS=1 python3 -B "$HERE/replay.py"
