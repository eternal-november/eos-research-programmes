#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
    test "$(git hash-object "$UP/$dest")" = "$sha"
    cp "$UP/$dest" "$D/$(basename "$dest")"
done < "$HERE/SOURCE.tsv"
cd "$D"
python3 -B extract_radio.py
python3 -B extract_visible.py
python3 -B "$HERE/project.py"
g++ -std=c++17 -O2 -Wno-return-type -I "$D" "$HERE/native_routes.cpp" -o "$D/route"
"$D/route" "$D/sites.tsv"
