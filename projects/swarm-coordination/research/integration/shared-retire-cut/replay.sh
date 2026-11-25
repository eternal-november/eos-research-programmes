#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
python3 -B "$ROOT/verify_inputs.py" "$UP"
cp "$UP"/subt/* "$D"
(cd "$D" && python3 -B extract.py)
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type -I "$UP" -I "$D" "$ROOT/subt_driver.cpp" -o "$D/subt"
PYTHONHASHSEED=0 python3 -B "$ROOT/transfer.py" "$UP" "$D/subt"
