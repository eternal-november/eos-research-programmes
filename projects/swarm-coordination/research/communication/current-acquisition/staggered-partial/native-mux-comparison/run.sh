#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r file repo commit path blob; do
    test "$(git hash-object "$up/$file")" = "$blob"
done < "$here/SOURCE.tsv"
PYTHONPATH="$up" python3 -B "$here/replay.py" "$up"
