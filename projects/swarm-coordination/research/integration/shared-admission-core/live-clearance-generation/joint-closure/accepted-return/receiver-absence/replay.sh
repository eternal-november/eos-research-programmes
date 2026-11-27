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
sed '/^int main()/,$d' "$up/broker.cpp" > "$tmp/pinned_broker.h"
g++ -std=c++17 -O2 -I "$tmp" "$here/wire.cpp" -o "$tmp/wire"
python3 -B "$here/extract.py" "$up" "$tmp/vda"
python3 -B "$here/transform.py" "$up" "$tmp/assembled.py"
PYTHONPATH="$up" python3 -B "$tmp/assembled.py" "$up" "$tmp/wire" "$tmp/vda"
