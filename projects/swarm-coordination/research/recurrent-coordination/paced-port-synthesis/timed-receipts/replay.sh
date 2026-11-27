#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r local repo ref source blob; do
    [ "$(git hash-object "$up/$local")" = "$blob" ]
done < "$here/SOURCE.tsv"
PYTHONPATH="$up" python3 -B "$here/replay.py"
