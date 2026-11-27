#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B extract.py
python3 -B extract_lifecycle.py
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type lifecycle.cpp -o lifecycle
./lifecycle
