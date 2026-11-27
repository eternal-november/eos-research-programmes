#!/bin/sh
set -eu
cd "$(dirname "$0")"
check() {
 while IFS="$(printf '\t')" read -r file repo rev path sha; do
  test "$(git hash-object "$file")" = "$sha"
 done < "$1"
}
check SENSOR_IMPORTS.tsv
(
 cd sensor
 check AUX_INPUTS.tsv
 python3 -B extract.py
 python3 -B extract_lifecycle.py
 python3 -B extract_publish.py
 "${CXX:-g++}" -std=c++20 -O2 -Wno-return-type shader_sensor.cpp -o frame
 cd radio
 check INPUTS.tsv
 python3 -B extract_radio.py
 "${CXX:-g++}" -std=c++17 -O2 -Wno-return-type motion_broker.cpp -o broker
)
python3 -B raster.py
python3 -B joined_raster.py
