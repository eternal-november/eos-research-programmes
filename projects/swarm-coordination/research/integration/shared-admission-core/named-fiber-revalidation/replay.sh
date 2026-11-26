#!/bin/sh
set -eu
# shared upstream root, #589, common interpreter, #596 study, #588 study, named, flight, #603 study.
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
prev=$(CDPATH= cd -- "$2" && pwd)
ack=$(CDPATH= cd -- "$8" && pwd)
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
t=$(printf '\t')
while IFS="$t" read -r file repo rev src hash; do
  test "$(git hash-object "$up/$file")" = "$hash"
done < "$ack/SOURCE.tsv"
for row in "$ack/replay.py:30bcebbaf32ccd9dfdcf97078d12eb9eb6216bc8" "$ack/wire.cpp:3d6d5cb49b86479996c4e7ea07720be0c92055ed" "$ack/SOURCE.tsv:01cee81074fe2f05eceaaf7afb8ef52dc7de77d2" "$2/driver.cpp:123dd5a5c6adf43477e7637f36598a6debf019fd"            "$3/core.py:687bf1250c6725992b6de696d0781d7948b4a89e"            "$4/spatial.py:ba2a4efafc15120373dfd0bc1e1942a94c34bd93"            "$5/gate.py:2f3efc2d3f147fd36000facf86e8f8ca2258f49f"            "$6/release.py:2b3da4f85d129bf1c31cd9d3594c537d5ec5c654"            "$7/guard.py:189ed7db9a796f9f083610d9fb3e7ef93c5b1080"
do
  test "$(git hash-object "${row%:*}")" = "${row##*:}"
done
cp "$up"/subt/* "$d"
(cd "$d" && python3 -B extract.py)
c++ -std=c++17 -O2 -Wno-return-type -I"$d" -I"$prev" "$ack/wire.cpp" -o "$d/wire"
python3 -B "$s/replay.py" "$d/wire" "$ack" "$3" "$4/spatial.py" "$up" "$5" "$6" "$7"
