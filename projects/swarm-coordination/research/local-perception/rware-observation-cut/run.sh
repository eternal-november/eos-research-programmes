#!/bin/sh
set -eu
cd "$(dirname "$0")"
while IFS="$(printf '\t')" read -r name repo rev source sha; do
  test "$(git hash-object "$name")" = "$sha"
done < SOURCE.tsv
export OPENBLAS_NUM_THREADS=1
python3 -B observation_cut.py
