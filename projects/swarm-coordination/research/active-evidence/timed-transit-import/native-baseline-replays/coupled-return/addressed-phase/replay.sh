#!/bin/sh
set -eu
cd "$(dirname "$0")"
base="$PWD"
while IFS="$(printf '\t')" read -r name repo ref path hash; do
  test "$(git hash-object "source/$name")" = "$hash"
done < PINS.tsv
(cd source; python3 -B extract_radio.py; python3 -B extract_visible.py; python3 -B "$base/project.py")
(cd source; cp "$base/addressed.cpp" addressed.cpp; "${CXX:-g++}" -std=c++17 -O2 -Wno-return-type addressed.cpp -o addressed)
python3 -B check.py "$base/source" | cmp expected.txt -
