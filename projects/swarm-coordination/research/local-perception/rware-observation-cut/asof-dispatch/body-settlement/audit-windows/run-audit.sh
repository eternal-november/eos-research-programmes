#!/bin/sh
set -eu
cd "$(dirname "$0")"
while IFS="$(printf '\t')" read -r name repo rev source sha; do
  test "$(git hash-object "$name")" = "$sha"
done < AUDIT_INPUTS.tsv
export OPENBLAS_NUM_THREADS=1
python3 -B recurrent_motion.py > native.check
cmp recurrent_motion.json native.check
python3 -B audit_windows.py > windows.check
cmp audit_windows.json windows.check
echo 'Matched 248 native histories, 16,356 output words and 37,886 union queries.'
