#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SRC=$(CDPATH= cd -- "$1" && pwd)
UP=$(CDPATH= cd -- "$2" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
python3 -B - "$ROOT/INHERITED.tsv" "$SRC" <<'PY'
from hashlib import sha1
from pathlib import Path
import sys
for item in Path(sys.argv[1]).read_text().splitlines():
    name,sha=item.split()
    b=(Path(sys.argv[2])/name).read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha,name
PY
python3 -B "$SRC/verify.py" "$UP"
cp "$UP"/subt/* "$D"
(cd "$D" && python3 -B extract.py)
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type -I "$UP" -I "$D" "$SRC/driver.cpp" -o "$D/subt"
python3 -B "$ROOT/native.py" "$UP" "$D/subt" "$SRC"
