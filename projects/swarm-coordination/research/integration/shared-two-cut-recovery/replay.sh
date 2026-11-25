#!/bin/sh
set -e
cd "$(dirname "$0")"
(cd subt && python3 -B extract.py)
bin=$(mktemp)
trap 'rm -f "$bin"' EXIT
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type network.cpp -o "$bin"
"$bin" > network.tsv
python3 -B warehouse.py > warehouse.tsv
python3 -B check.py "$bin"
