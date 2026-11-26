#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
OLD=$(CDPATH= cd -- "$1" && pwd)
UP=$(CDPATH= cd -- "$2" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
(cd "$OLD" && sha256sum -c "$ROOT/adapter.sha256" >&2)
python3 -B "$OLD/verify_inputs.py" "$UP"
cp "$UP"/subt/* "$D"
(cd "$D" && python3 -B extract.py)
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type -I "$UP" -I "$D"  "$OLD/scope/driver.cpp" -o "$D/subt"
PYTHONHASHSEED=0 python3 -B "$ROOT/native.py" "$OLD/scope" "$UP" "$D/subt"
