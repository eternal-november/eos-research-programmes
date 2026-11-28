#!/bin/sh
set -eu
cd "$(dirname "$0")/source"
while IFS="$(printf '\t')" read -r name repo ref path hash; do
  test "$(git hash-object "$name")" = "$hash"
done < PINS.tsv
sh run.sh
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type receipt_stage.cpp -o receipt_stage
./receipt_stage
