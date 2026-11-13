#!/bin/sh
# Verify both interpreter modes and compare with the committed expected output.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT HUP INT TERM
python3 "$here/joint_gluing_checks.py" > "$work/normal.txt"
python3 -O "$here/joint_gluing_checks.py" > "$work/optimized.txt"
cmp "$work/normal.txt" "$work/optimized.txt"
cmp "$here/expected_output.txt" "$work/normal.txt"
cat "$work/normal.txt"
printf '%s\n' 'NORMAL AND -O OUTPUTS MATCH EXPECTED OUTPUT BYTE-FOR-BYTE'
