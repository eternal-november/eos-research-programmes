#!/bin/sh
set -eu
cd "$(dirname "$0")"
test "$(git hash-object upstream_replay.cpp)" = 8fcff1aa0e7052c2c0038644e5c206f1dab3841b
python3 -B extract_radio.py
python3 -B extract_visible.py
python3 -B build_labels.py
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type receipt_labels.cpp -o receipt_labels
python3 -B check_labels.py
