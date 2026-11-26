#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
HASH=$(cut -f5 "$HERE/SOURCE.tsv")
test "$(git hash-object "$UP/recurrence.py")" = "$HASH"
PYTHONPATH="$UP" python3 -B "$HERE/replay.py"
