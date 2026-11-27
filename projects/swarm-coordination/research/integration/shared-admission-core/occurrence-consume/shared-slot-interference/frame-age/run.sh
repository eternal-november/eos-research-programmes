#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r name repo sha source blob; do
    test "$(git hash-object "$up/$name")" = "$blob"
done < "$here/SOURCE.tsv"
python3 -B "$here/replay.py" "$up"
