#!/bin/sh
set -eu
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
RF=$(CDPATH= cd -- "$5" && pwd)
CORE=$(CDPATH= cd -- "$6" && pwd)
python3 -B "$CORE/verify.py" "$2" "$3" "$4" "$5"
python3 -B "$ROOT/spatial.py" "$UP" "$2" "$3" "$4" 0 > "$D/plain.json"
python3 -B "$ROOT/spatial.py" "$UP" "$2" "$3" "$4" 1 > "$D/held.json"
python3 -B "$RF/verify.py" "$UP"
cp "$UP"/subt/* "$D"
(cd "$D" && python3 -B extract.py)
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type -I "$D" -I "$RF" "$ROOT/radio.cpp" -o "$D/radio"
python3 -B "$ROOT/replay.py" "$D" "$CORE" "$UP" "$2" "$3" "$4"
