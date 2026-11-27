#!/bin/sh
set -eu
cd "$(dirname "$0")"
sh replay.sh | cmp expected_joined.txt -
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type readonly.cpp -o bridge
python3 -B compare.py
