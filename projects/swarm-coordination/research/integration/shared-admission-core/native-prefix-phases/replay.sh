#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
TAB=$(printf '\t')
while IFS="$TAB" read -r dest repo rev original sha; do
    test -n "$dest"
    test "$(git hash-object "$UP/$dest")" = "$sha"
    case "$dest" in subt/*) cp "$UP/$dest" "$D/$(basename "$dest")";; esac
done < "$HERE/SOURCE.tsv"
(cd "$D" && python3 -B extract.py)
g++ -std=c++17 -O2 -Wno-return-type -I "$D" "$HERE/native.cpp" -o "$D/native"
PYTHONPATH="$UP" python3 -B "$HERE/replay.py" "$UP" "$D/native"
