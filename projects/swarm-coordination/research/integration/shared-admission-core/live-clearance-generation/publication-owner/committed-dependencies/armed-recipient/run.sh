#!/bin/sh
set -eu
cd "$(dirname "$0")"
UP=$(CDPATH= cd -- "${1:-inputs}" && pwd)
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
  test "$(git hash-object "$UP/$dest")" = "$sha"
done < SOURCE.tsv
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
  test "$(git hash-object "$dest")" = "$sha"
done < LOCAL.tsv
export PYTHONPATH="$UP" OPENBLAS_NUM_THREADS=1
python3 -B grant.py "$UP" > actual_grant.json
cmp actual_grant.json expected_grant.json
python3 -B armed.py "$UP" > actual_armed.json
cmp actual_armed.json expected_armed.json
python3 -B state_law.py > actual_state.json
cmp actual_state.json expected_state.json
printf '%s\n' 'All native and projected comparisons matched.'
