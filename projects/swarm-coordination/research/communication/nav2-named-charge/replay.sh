#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B extract.py
t=$(mktemp)
trap 'rm -f "$t"' EXIT
"${CXX:-g++}" -std=c++17 -O2 replay.cpp -o "$t"
"$t"
