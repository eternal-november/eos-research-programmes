#!/bin/sh
set -eu
cd "$(dirname "$0")"
src="${1:-../source}"
while IFS="$(printf '\t')" read -r name repo ref path hash; do
  test "$(git hash-object "$src/$name")" = "$hash"
done < ../SOURCE_INPUTS.tsv
(cd "$src"; python3 -B extract_radio.py; python3 -B extract_visible.py)
python3 -B chords.py | cmp expected.txt -
cmp expected-paths.json chord-results.json
python3 -B radio_static.py "$src" | cmp expected-radio.txt -
