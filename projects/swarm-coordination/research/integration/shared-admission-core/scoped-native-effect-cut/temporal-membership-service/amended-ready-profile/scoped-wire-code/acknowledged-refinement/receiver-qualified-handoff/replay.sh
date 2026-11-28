#!/bin/sh
set -eu
H=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
U=$(CDPATH= cd -- "$1" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
while IFS="$(printf '\t')" read -r dest repo rev path sha; do
  test "$(git hash-object "$U/$dest")" = "$sha"
  cp "$U/$dest" "$D/$(basename "$dest")"
done < "$H/SOURCE.tsv"
cd "$D"
python3 -B extract_radio.py
python3 -B extract_visible.py
python3 -B "$H/membership.py"
python3 -B "$H/parent.py"
python3 -B "$H/temporal.py"
python3 -B "$H/refinement.py"
python3 -B "$H/handoff.py"
g++ -O2 -std=c++17 -Wno-return-type -I . "$H/checks.cpp" -o checks
./checks
