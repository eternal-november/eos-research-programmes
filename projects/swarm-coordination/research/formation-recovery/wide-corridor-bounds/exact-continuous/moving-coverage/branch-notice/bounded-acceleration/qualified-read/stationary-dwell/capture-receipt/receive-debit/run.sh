#!/bin/sh
set -eu
cd "$(dirname "$0")"
while IFS="$(printf '\t')" read -r name repo rev source sha; do
  test "$(git hash-object "$name")" = "$sha"
done < INPUTS.tsv
python3 -B extract_radio.py
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type motion_broker.cpp -o broker
python3 -B joined.py
