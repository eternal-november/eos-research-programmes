#!/bin/sh
set -eu
cd "$(dirname "$0")"
test "$(git hash-object upstream_replay.cpp)" = 8fcff1aa0e7052c2c0038644e5c206f1dab3841b
python3 -B extract.py
bin=$(mktemp)
trap 'rm -f "$bin"' EXIT
"${CXX:-g++}" -Wno-return-type -std=c++17 -O2 joined_gate.cpp -o "$bin"
"$bin"
