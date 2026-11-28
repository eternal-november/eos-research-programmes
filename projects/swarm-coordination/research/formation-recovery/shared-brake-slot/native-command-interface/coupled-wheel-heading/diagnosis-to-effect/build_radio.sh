#!/bin/bash
set -euo pipefail
base=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
while IFS=$'\t' read -r name repo path rev blob; do
  test "$(git hash-object "$base/$name")" = "$blob"
done < "$base/INPUTS.tsv"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
out=$1
cp "$base"/source/* "$base/radio.cc" "$tmp"
cd "$tmp"
cp broker.cc src0; cp model.cc src3; cp table.cc src4
python3 -B extract_visible.py
python3 -B extract_radio.py
g++ -std=c++17 -O2 -Wno-return-type -c radio.cc -o "$out"
