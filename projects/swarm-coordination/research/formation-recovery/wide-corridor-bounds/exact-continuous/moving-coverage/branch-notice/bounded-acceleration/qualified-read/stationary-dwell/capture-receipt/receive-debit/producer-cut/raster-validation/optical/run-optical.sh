#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
sh run.sh >/dev/null
(
 cd optical/rware
 while IFS="$(printf '\t')" read -r local repo rev path sha; do
  test "$(git hash-object "$local")" = "$sha"
 done < INPUTS.tsv
)
cp optical/optical_sensor.cpp sensor/
cp optical/rf_cut.cpp sensor/radio/
python3 -B optical/extract_color.py
(cd sensor; "${CXX:-g++}" -std=c++20 -O2 -Wno-return-type optical_sensor.cpp -o color-frame)
(cd sensor/radio; "${CXX:-g++}" -std=c++17 -O2 -Wno-return-type rf_cut.cpp -o rf-cut)
python3 -B optical/join_optical.py
