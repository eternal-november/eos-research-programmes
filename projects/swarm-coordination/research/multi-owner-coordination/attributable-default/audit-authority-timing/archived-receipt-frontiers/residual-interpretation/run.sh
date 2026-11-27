#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r n repo rev path blob; do
    test "$(git hash-object "$up/$n")" = "$blob"
done < "$here/SOURCE.tsv"
python3 -B "$here/interpret.py" "$up"
