#!/bin/sh
set -e
cd "$(dirname "$0")"
python3 -B extract.py
bin=$(mktemp)
trap 'rm -f "$bin"' EXIT
"${CXX:-g++}" -std=c++17 -O2 replay.cpp -o "$bin"
"$bin"
