#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r local repo ref source blob; do
    [ "$(git hash-object "$up/$local")" = "$blob" ]
done < "$here/SOURCE.tsv"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
cp "$up"/subt/src? "$up"/subt/replay.cpp "$up"/subt/extract.py "$tmp"/
(cd "$tmp"; python3 extract.py)
g++ -std=c++17 -O2 -I "$tmp" "$here/cuts.cpp" -o "$tmp/cuts"
PYTHONPATH="$up" python3 -B "$here/replay.py" "$up" "$tmp/cuts"
