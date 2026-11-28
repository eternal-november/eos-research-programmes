#!/bin/sh
set -eu
H=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
O=$(CDPATH= cd -- "$1" && pwd)
F=$(CDPATH= cd -- "$2" && pwd)
U=$(CDPATH= cd -- "$3" && pwd)
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
cp -r "$F"/. "$T"/
cp "$O/mission.cpp" "$T/old.cpp"
cp "$H/sanitizer_single.py" "$T/"
cd "$T"
python3 - "$H/REPLAY_PATCH.tsv" <<'PY'
from pathlib import Path
from hashlib import sha256
import sys
k,r,c,b,a,o=next(s.split("\t") for s in Path(sys.argv[1]).read_text().splitlines() if s.startswith("904\t"))
assert sha256(Path("old.cpp").read_bytes()).hexdigest()==b
assert sha256(Path("mission.cpp").read_bytes()).hexdigest()==a
p=Path("replay.sh")
s=p.read_text()
a=s.index('g++ -O2')
s=s[:a]+"""for target in mission old; do
  g++ -O1 -g -std=c++17 -Wno-return-type -fno-omit-frame-pointer -fsanitize=address -fsanitize-address-use-after-scope -I . "$H/$target.cpp" -o "$target"
done
export ASAN_OPTIONS=detect_stack_use_after_return=1:detect_leaks=0
python3 -B "$H/sanitizer_single.py" ./mission sites.tsv poses.json > passed.json
python3 -B -c 'import json; p=json.load(open("passed.json")); assert p["ack"] and not p["overlap"]'
if python3 -B "$H/sanitizer_single.py" ./old sites.tsv poses.json > old.log 2>&1; then
  exit 1
fi
grep -q stack-use-after-scope old.log
echo 'original: stack-use-after-scope; restored: exact representative trace'
"""
p.write_text(s)
PY
bash replay.sh "$U" parent
