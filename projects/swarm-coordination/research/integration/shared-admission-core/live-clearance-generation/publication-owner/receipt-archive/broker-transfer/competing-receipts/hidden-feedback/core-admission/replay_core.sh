#!/bin/sh
set -eu
cd "$(dirname "$0")"
test "$(git hash-object core.py)" = 687bf1250c6725992b6de696d0781d7948b4a89e
test "$(git hash-object upstream_replay.cpp)" = 8fcff1aa0e7052c2c0038644e5c206f1dab3841b
python3 -B extract_radio.py
python3 -B extract_score.py
"${CXX:-g++}" -Wno-return-type -std=c++17 -O2 native.cpp -o native
"${CXX:-g++}" -std=c++17 -O2 score.cpp -o score
./score | cmp expected_score.txt -
python3 -B run_core.py
