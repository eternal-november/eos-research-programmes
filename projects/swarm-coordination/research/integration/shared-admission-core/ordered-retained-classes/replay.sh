#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
    test "$(git hash-object "$UP/$dest")" = "$sha"
done < "$HERE/SOURCE.tsv"
PYTHONHASHSEED=0 PYTHONPATH="$UP:$UP/simu" python3 -B "$HERE/replay.py" "$UP"
