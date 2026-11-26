#!/bin/sh
set -eu
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
prior=$(CDPATH= cd -- "$2" && pwd)
t=$(printf '\t')
while IFS="$t" read -r file repo rev path hash; do
  test "$(git hash-object "$up/$file")" = "$hash"
done < "$s/SOURCE.tsv"
test "$(git hash-object "$prior/driver.cpp")" = "123dd5a5c6adf43477e7637f36598a6debf019fd"
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$up"/subt/* "$d"
(cd "$d" && python3 -B extract.py)
c++ -std=c++17 -O2 -Wno-return-type -I"$d" -I"$prior" "$s/route.cpp" -o "$d/radio"
python3 -B "$s/replay.py" "$d/radio" "$3"
