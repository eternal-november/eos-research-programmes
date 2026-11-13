#!/bin/sh
set -eu
cd "$(dirname "$0")"
a=$(mktemp)
b=$(mktemp)
trap 'rm -f "$a" "$b"' EXIT HUP INT TERM
python exact_transport_checks.py > "$a"
python -O exact_transport_checks.py > "$b"
cmp "$a" "$b"
cmp "$a" exact_transport_expected.txt
cat "$a"
printf '%s\n' 'Normal and optimized runs match the recorded expected output.'
