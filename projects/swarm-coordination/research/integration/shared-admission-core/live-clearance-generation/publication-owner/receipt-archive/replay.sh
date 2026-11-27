#!/bin/sh
set -eu
cd "$(dirname "$0")"
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
  test "$(git hash-object "$dest")" = "$sha"
done < warehouse_SOURCE.tsv
python3 -B extract.py
"${CXX:-g++}" -std=c++17 -O2 score.cpp -o score
./score | cmp expected_score.txt -
OPENBLAS_NUM_THREADS=1 python3 -B warehouse_replay.py "$PWD" > warehouse_check.json
cmp expected_warehouse.txt warehouse_check.json
OPENBLAS_NUM_THREADS=1 python3 -B archive.py
