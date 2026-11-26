#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
python3 -B "$ROOT/extract.py" "$1" "$D/subscription.inc"
"${CXX:-g++}" -std=c++17 -O2 -I "$D" "$ROOT/replay.cpp" -o "$D/replay"
"$D/replay"
python3 -B "$ROOT/matching.py"
