#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r name repo commit path blob; do
    test "$(git hash-object "$up/$name")" = "$blob"
done < "$here/SOURCE.tsv"
w=$(mktemp -d)
trap 'rm -rf "$w"' EXIT HUP INT TERM
(cd "$w"; python3 -B "$here/extract.py" "$up")
g++ -std=c++17 -Wall -Wextra -Wno-missing-field-initializers -O2 -I "$w" "$here/radio.cpp" -o "$w/radio"
python3 -B "$here/replay.py" "$up" "$w/radio"
