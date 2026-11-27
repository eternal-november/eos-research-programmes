#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
(cd "$here"; sha256sum -c CONSUMER.sha256 >&2)
while IFS="$(printf '\t')" read -r name repo sha source blob; do
    test "$(git hash-object "$up/$name")" = "$blob"
done < "$here/SOURCE.tsv"
PYTHONPATH="$up/radio" OPENBLAS_NUM_THREADS=1 python3 -B "$here/replay.py" "$up"
