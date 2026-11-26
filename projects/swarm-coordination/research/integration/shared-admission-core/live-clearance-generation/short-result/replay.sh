#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
    test "$(git hash-object "$UP/$dest")" = "$sha"
    case "$dest" in subt/*) cp "$UP/$dest" "$D/$(basename "$dest")";; esac
done < "$HERE/SOURCE.tsv"
(cd "$D" && python3 -B extract.py)
sed "s/^int main()/int pinned_main()/" "$UP/broker.cpp" > "$D/pinned_broker.h"
patch --batch -s -o "$D/wire.cpp" "$UP/parent.cpp" "$HERE/wire.patch"
patch --batch -s -o "$D/replay.py" "$UP/parent.py" "$HERE/replay.patch"
g++ -std=c++17 -O2 -Wno-return-type -I "$UP" -I "$D" "$D/wire.cpp" -o "$D/wire"
PYTHONPATH="$UP" OPENBLAS_NUM_THREADS=1 python3 -B "$D/replay.py" "$UP" "$D/wire"
