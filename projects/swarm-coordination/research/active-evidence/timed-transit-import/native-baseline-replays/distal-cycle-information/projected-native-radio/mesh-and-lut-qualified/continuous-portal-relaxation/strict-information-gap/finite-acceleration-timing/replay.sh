#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r dest repo rev path sha; do
  test "$(git hash-object "$UP/$dest")" = "$sha"
done < "$HERE/PARENT_INPUTS.tsv"
python3 -B "$HERE/timing.py" "$UP/paths.json" "$UP/EXPECTED.jsonl"
