#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
OLD=$(CDPATH= cd -- "$2" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
python3 -B "$ROOT/verify.py" "$UP"
python3 -B - "$OLD/driver.cpp" <<'PY'
from pathlib import Path
from hashlib import sha1
import sys
x=Path(sys.argv[1]).read_bytes()
assert sha1(f"blob {len(x)}\0".encode()+x).hexdigest()=="123dd5a5c6adf43477e7637f36598a6debf019fd"
PY
cp "$UP"/subt/* "$D"
(cd "$D" && python3 -B extract.py)
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type -I "$D" -I "$OLD" "$ROOT/native.cpp" -o "$D/native"
python3 -B "$ROOT/checks.py" "$D/native" "$3"
