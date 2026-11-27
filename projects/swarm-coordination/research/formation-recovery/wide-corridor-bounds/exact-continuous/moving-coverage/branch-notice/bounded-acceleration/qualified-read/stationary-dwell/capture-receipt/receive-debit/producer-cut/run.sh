#!/bin/sh
set -eu
cd "$(dirname "$0")"
while IFS="$(printf '\t')" read -r local repo rev path sha; do
 test "$(git hash-object "$local")" = "$sha"
done < AUX_INPUTS.tsv
python3 -B extract.py
python3 -B extract_lifecycle.py
python3 -B extract_publish.py
"${CXX:-g++}" -std=c++20 -O2 -Wno-return-type capture.cpp -o sensor
(
 cd radio
 while IFS="$(printf '\t')" read -r local repo rev path sha; do
  test "$(git hash-object "$local")" = "$sha"
 done < INPUTS.tsv
 python3 -B extract_radio.py
 "${CXX:-g++}" -std=c++17 -O2 -Wno-return-type motion_broker.cpp -o broker
)
python3 -B joint_sensor.py
