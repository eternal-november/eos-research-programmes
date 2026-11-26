#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
INHERITED=$(CDPATH= cd -- "$1" && pwd)
UP=$(CDPATH= cd -- "$2" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
python3 -B - "$ROOT/INHERITED.tsv" "$INHERITED" <<'EOF'
from hashlib import sha1
from pathlib import Path
import sys
for name,expected in (row.split() for row in Path(sys.argv[1]).read_text().splitlines()):
    value=(Path(sys.argv[2])/name).read_bytes()
    assert sha1(f"blob {len(value)}\0".encode()+value).hexdigest()==expected, name
EOF
python3 -B "$INHERITED/verify.py" "$UP"
cp "$UP"/subt/* "$D"
(cd "$D" && python3 -B extract.py)
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type -I "$UP" -I "$D" "$INHERITED/driver.cpp" -o "$D/subt"
PYTHONHASHSEED=0 python3 -B "$ROOT/replay.py" "$D/subt"
