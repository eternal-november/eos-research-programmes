#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r local repo ref path hash; do
    test "$(git hash-object "$up/$local")" = "$hash"
done < "$here/SOURCE.tsv"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
(cd "$work"; python3 -B "$here/extract.py" "$up")
g++ -std=c++17 -O2 -I "$work" "$here/connector.cpp" -o "$work/test"
python3 -B "$here/replay.py" "$up" "$work/test"
