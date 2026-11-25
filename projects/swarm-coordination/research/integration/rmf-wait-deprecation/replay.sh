#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B extract.py
CXX=${CXX:-g++}
bin=$(mktemp)
trap 'rm -f "$bin"' EXIT
"$CXX" -std=c++17 -O2 -Wall -Wextra harness.cpp -o "$bin"
"$bin"
