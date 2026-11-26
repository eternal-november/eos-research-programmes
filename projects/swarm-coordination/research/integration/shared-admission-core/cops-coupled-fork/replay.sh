#!/bin/sh
set -eu
# COPS dir, shared core, SubT source parent, #589 replay directory
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
up=$(CDPATH= cd -- "$3" && pwd)
prior=$(CDPATH= cd -- "$4" && pwd)
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
t=$(printf '\t')
while IFS="$t" read -r file repo rev path hash; do
  test "$(git hash-object "$up/$file")" = "$hash"
done < "$s/SUBT.tsv"
test "$(git hash-object "$prior/driver.cpp")" = "123dd5a5c6adf43477e7637f36598a6debf019fd"
cp "$up"/subt/* "$d"
(cd "$d" && python3 -B extract.py)
c++ -std=c++17 -O2 -Wno-return-type -I"$d" -I"$prior" "$s/contact.cpp" -o "$d/radio"
python3 -B "$s/replay.py" "$1" "$2" "$d/radio"
