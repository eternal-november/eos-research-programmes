#!/bin/sh
set -eu
cd "$(dirname "$0")"
test "$(git hash-object upstream_replay.cpp)" = 8fcff1aa0e7052c2c0038644e5c206f1dab3841b
python3 -B extract_radio.py
python3 -B extract_score.py
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type bridge.cpp -o bridge
"${CXX:-g++}" -std=c++17 -O2 score.cpp -o score
./score | cmp expected_score.txt -
python3 -B joined.py
