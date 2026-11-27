#!/bin/sh
set -eu
cd "$(dirname "$0")"
test "$(git hash-object upstream_replay.cpp)" = 8fcff1aa0e7052c2c0038644e5c206f1dab3841b
python3 -B extract_radio.py
python3 -B extract_visible.py
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type gate_budget.cpp -o gate_budget
python3 -B gate_budget.py
