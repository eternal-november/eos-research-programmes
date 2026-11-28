#!/bin/sh
set -eu
cd "$(dirname "$0")"
base="$PWD"
while IFS="$(printf '\t')" read -r name repo ref path hash; do
  test "$(git hash-object "source/$name")" = "$hash"
done < SOURCE_INPUTS.tsv
(cd source; python3 -B extract_radio.py; python3 -B extract_visible.py)
python3 -B egress.py | cmp expected-mesh.txt -
python3 -B timeline.py | cmp expected-timing.txt -
python3 -B radio_timeline.py "$base/source" | cmp expected-radio.txt -
