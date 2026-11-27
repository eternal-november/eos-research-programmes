#!/bin/sh
set -eu
cd "$(dirname "$0")"
while IFS="$(printf '\t')" read -r name repo rev source sha; do
  test "$(git hash-object "$name")" = "$sha"
done < INPUTS.tsv
python3 -B extract_radio.py
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type deliver.cpp -o deliver
export OPENBLAS_NUM_THREADS=1
python3 -B joint.py
