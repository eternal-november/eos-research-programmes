#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B extract.py
python3 -B extract_lifecycle.py
python3 -B extract_guard.py
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type guard_traces.cpp -o guard_traces
./guard_traces > guard_traces.tsv
python3 -B guard_cuts.py < guard_traces.tsv
