#!/bin/sh
set -eu
# source parent, Eigen include, prior study, warehouse upstream, sp, named, flight, core.
root=$(CDPATH= cd -- "$1" && pwd)
eigen=$2
prior=$(CDPATH= cd -- "$3" && pwd)
study=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
t=$(printf '\t')
while IFS="$t" read -r repo rev hash file; do
  test "$(git hash-object "$root/$file")" = "$hash"
done < "$prior/SOURCE.tsv"
test "$(git hash-object "$prior/replay.cc")" = "f71aca0f529321b4e906526b90c8730e044c7c57"
test "$(git hash-object "$5/native.py")" = "9d0e3c4191a064c37a3d5d04ba5619f58a70617d"
test "$(git hash-object "$5/gate.py")" = "2f3efc2d3f147fd36000facf86e8f8ca2258f49f"
test "$(git hash-object "$7/guard.py")" = "189ed7db9a796f9f083610d9fb3e7ef93c5b1080"
test "$(git hash-object "$6/release.py")" = "2b3da4f85d129bf1c31cd9d3594c537d5ec5c654"
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
python3 -B "$5/native.py" "$4" "$6" "$7" > "$d/space.json"
c++ -std=c++17 -O1 -Wno-return-type -I"$eigen" -I"$root/rmf_traffic/include" -I"$root/rmf_utils/include" -I"$prior" \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/Constraint.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/Moderator.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/Participant.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/Rectifier.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/conflicts.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/geometry.cpp "$study/source.cc" -o "$d/test"
python3 -B "$study/replay.py" "$d/test" "$d/space.json" "$8"
