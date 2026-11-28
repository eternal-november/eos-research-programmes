#!/bin/sh
set -eu
H=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
U=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r n ref src h; do
  test "$(git hash-object "$U/$n")" = "$h"
done < "$H/SOURCE.tsv"
python3 -B "$H/risk.py" "$U"
