#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
while IFS="$(printf '\t')" read -r local repo ref source blob; do
    test "$(git hash-object "$up/$local")" = "$blob"
done < "$here/SOURCE.tsv"
cp "$up"/subt/src? "$up"/subt/replay.cpp "$up"/subt/extract.py "$up"/scope.cpp "$d"/
(cd "$d"; python3 -B extract.py; python3 -B "$up/pose-extract.py"; python3 -B "$here/prepare.py")
g++ -std=c++17 -O2 -Wno-return-type -I "$d" "$here/replay.cpp" -o "$d/replay"
PYTHONPATH="$up" OPENBLAS_NUM_THREADS=1 python3 -B "$here/replay.py" "$up" "$d/replay"
