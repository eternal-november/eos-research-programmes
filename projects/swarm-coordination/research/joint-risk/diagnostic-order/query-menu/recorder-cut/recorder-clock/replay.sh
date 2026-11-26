#!/bin/sh
set -eu
# First argument is directory with pinned upstream recorder.cpp and writer.hpp, second is parent #488 study path.
self=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
parent=$(CDPATH= cd -- "$2" && pwd)
temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT
python3 "$parent/extract.py" "$1" "$temp/subscription.inc"
cp "$parent/replay.cpp" "$temp/replay.cpp"
c++ -std=c++20 -Wno-return-type -I"$temp" "$self/recorder_cases.cc" -o "$temp/replay"
"$temp/replay" < "$self/inputs.tsv" > "$temp/rows.txt"
python3 "$self/risk_clock.py" "$temp/rows.txt"
