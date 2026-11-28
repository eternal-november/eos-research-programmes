#!/bin/sh
set -eu
cd "$(dirname "$0")"
base="$PWD"
while IFS="$(printf '\t')" read -r name repo ref path hash; do
  test "$(git hash-object "source/$name")" = "$hash"
done < PINS.tsv
(cd source; python3 -B extract_radio.py; python3 -B extract_visible.py)
python3 -B project.py "$base/source"
out=$(mktemp)
trap 'rm -f "$out"' EXIT
(cd source; cp "$base/native.cpp" motion_native.cpp
 "${CXX:-g++}" -std=c++17 -O2 -Wno-return-type motion_native.cpp -o "$out"; "$out") | cmp contacts.tsv -
python3 -B coupled.py "$base/source" | cmp expected-common.txt -
python3 -B local.py "$base/source" | cmp expected-local.txt -
python3 -B witness.py "$base/source" | cmp expected-witness.txt -
