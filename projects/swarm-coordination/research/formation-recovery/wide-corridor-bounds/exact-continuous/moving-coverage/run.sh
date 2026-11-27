#!/bin/sh
set -eu
cd "$(dirname "$0")"
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
  test "$(git hash-object "$dest")" = "$sha"
done < MOVING_INPUTS.tsv
export OPENBLAS_NUM_THREADS=1
python3 -B moving.py
