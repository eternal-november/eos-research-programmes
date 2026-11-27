#!/bin/sh
set -eu
cd "$(dirname "$0")"
(cd ..; python3 -B extract.py)
python3 -B derive.py
"${CXX:-g++}" -std=c++20 -O2 -Wno-return-type check.cpp -o wirecheck
./wirecheck
