#!/bin/sh
set -eu
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
SP=$(CDPATH= cd -- "$2" && pwd)
RF=$(CDPATH= cd -- "$5" && pwd)
python3 -B "$ROOT/verify.py" "$SP" "$3" "$4" "$RF"
python3 -B "$SP/native.py" "$UP" "$3" "$4" > "$D/spatial.json"
python3 -B "$RF/verify.py" "$UP"
cp "$UP"/subt/* "$D"
(cd "$D" && python3 -B extract.py)
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type -I "$D" -I "$RF" "$ROOT/native.cpp" -o "$D/radio"
python3 -B "$ROOT/replay.py" "$D/spatial.json" "$D/radio"
