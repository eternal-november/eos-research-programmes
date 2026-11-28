#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
    test "$(git hash-object "$UP/$dest")" = "$sha"
    case "$dest" in vis/*) cp "$UP/$dest" "$D/$(basename "$dest")";; esac
done < "$HERE/SOURCE.tsv"
(cd "$D" && python3 -B extract_radio.py && python3 -B extract_visible.py && python3 -B project_graph.py)
sed -e 's/"replay.cpp"/"staged_replay.inc"/' -e 's/^int main()/int pinned_main()/' "$UP/broker.cpp" > "$D/pinned_broker.h"
g++ -std=c++17 -O2 -Wno-return-type -I "$D" "$HERE/radio_wire.cpp" -o "$D/wire"
PYTHONPATH="$UP" OPENBLAS_NUM_THREADS=1 python3 -B "$HERE/replay.py" "$UP" "$D/wire" "$D/distances.tsv"
