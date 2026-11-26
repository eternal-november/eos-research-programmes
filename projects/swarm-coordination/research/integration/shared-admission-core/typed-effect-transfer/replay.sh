#!/bin/sh
set -eu
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
timed=$(CDPATH= cd -- "$2" && pwd)
radio=$(CDPATH= cd -- "$3" && pwd)
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
t=$(printf '\t')
test "$(git hash-object "$8/SOURCE.tsv")" = '01cee81074fe2f05eceaaf7afb8ef52dc7de77d2'
while IFS="$t" read -r file repo rev path hash; do
  test "$(git hash-object "$up/$file")" = "$hash"
done < "$8/SOURCE.tsv"
for f in "$timed/driver.cpp:123dd5a5c6adf43477e7637f36598a6debf019fd" \
 "$radio/gate.cpp:0276e26eec15a21baf608620ba2137d8958d4185" \
 "$4/replay.py:26985aecb10fe956eb75e4d50c92ac0d256671fa" \
 "$5/native.py:3c8870664b7bd6054cd756a6ffc7c365d8aae0c6" \
 "$5/guard.py:189ed7db9a796f9f083610d9fb3e7ef93c5b1080" \
 "$6/native.py:dcba6da00966bb61d72134662947d429ea1a6c35" \
 "$6/release.py:2b3da4f85d129bf1c31cd9d3594c537d5ec5c654" \
 "$7/core.py:687bf1250c6725992b6de696d0781d7948b4a89e"
do test "$(git hash-object "${f%:*}")" = "${f##*:}"; done
cp "$up"/subt/* "$d"
(cd "$d" && python3 -B extract.py)
c++ -std=c++17 -O2 -Wno-return-type -I"$d" -I"$timed" "$radio/gate.cpp" -o "$d/gate"
python3 -B "$s/replay.py" "$d/gate" "$4/replay.py" "$1" "$5" "$6" "$7"
