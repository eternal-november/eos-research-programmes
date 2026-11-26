#!/bin/sh
set -eu
# upstream COPS, #600 fixture, core, SubT parent, #589 driver, #596 study,
# warehouse upstream, #588 producer, named withdrawal, flight study
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$4" && pwd)
prior=$(CDPATH= cd -- "$5" && pwd)
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
t=$(printf '\t')
while IFS="$t" read -r file repo rev path hash; do
  test "$(git hash-object "$up/$file")" = "$hash"
done < "$s/SUBT.tsv"
for row in "$5/driver.cpp:123dd5a5c6adf43477e7637f36598a6debf019fd"           "$2/bridge.py:36649944eb36354b05fec5caa1fb5a88109d4591"           "$2/replay.py:9e57812c4beb63f79adbbefd2b3eda11f57f5f8f"           "$6/spatial.py:ba2a4efafc15120373dfd0bc1e1942a94c34bd93"           "$8/gate.py:2f3efc2d3f147fd36000facf86e8f8ca2258f49f"           "$9/release.py:2b3da4f85d129bf1c31cd9d3594c537d5ec5c654"           "${10}/guard.py:189ed7db9a796f9f083610d9fb3e7ef93c5b1080"
do
  test "$(git hash-object "${row%:*}")" = "${row##*:}"
done
cp "$up"/subt/* "$d"
(cd "$d" && python3 -B extract.py)
c++ -std=c++17 -O2 -Wno-return-type -I"$d" -I"$prior" "$s/gate.cpp" -o "$d/radio"
python3 -W ignore::SyntaxWarning -B "$s/replay.py" "$1" "$3" "$2" "$d/radio" "$6/spatial.py" "$7" "$8" "$9" "${10}"
