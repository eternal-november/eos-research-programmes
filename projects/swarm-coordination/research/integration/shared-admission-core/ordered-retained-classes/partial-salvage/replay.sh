#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$1
while IFS="$(printf '\t')" read -r local repo ref source blob; do
    [ "$(git hash-object "$up/$local")" = "$blob" ]
done < "$here/SOURCE.tsv"
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$up" python "$here/replay.py" "$up"
