#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
python3 -B "$ROOT/extract.py" "$1" "$D"
"${CXX:-g++}" -std=c++17 -O2 -pthread -I "$D" "$ROOT/replay.cpp" -o "$D/native"
"$D/native"
