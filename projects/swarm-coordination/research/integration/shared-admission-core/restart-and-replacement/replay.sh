#!/bin/sh
set -eu
# Inputs: upstream SubT root, native timed producer, shared admission, ACK window.
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
prev=$(CDPATH= cd -- "$2" && pwd)
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
t=$(printf '\t')
test "$(git hash-object "$4/SOURCE.tsv")" = '01cee81074fe2f05eceaaf7afb8ef52dc7de77d2'
while IFS="$t" read -r file repo rev path hash; do
  case "$file" in subt/*) test "$(git hash-object "$up/$file")" = "$hash";; esac
done < "$4/SOURCE.tsv"
test "$(git hash-object "$prev/driver.cpp")" = '123dd5a5c6adf43477e7637f36598a6debf019fd'
test "$(git hash-object "$3/core.py")" = '687bf1250c6725992b6de696d0781d7948b4a89e'
cp "$up"/subt/* "$d"
(cd "$d" && python3 -B extract.py)
c++ -std=c++17 -O2 -Wno-return-type -I"$d" -I"$prev" "$s/gate.cpp" -o "$d/gate"
python3 -B "$s/replay.py" "$d/gate" "$3"
