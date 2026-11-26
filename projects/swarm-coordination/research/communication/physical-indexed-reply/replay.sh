#!/bin/sh
set -eu
# AprilTag root, SubT parent, #589 fixture, #596 fixture, RWARE parent, #588 source, named, flight.
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ap=$(CDPATH= cd -- "$1" && pwd)
up=$(CDPATH= cd -- "$2" && pwd)
prior=$(CDPATH= cd -- "$3" && pwd)
t=$(printf '\t')
while IFS="$t" read -r file hash; do
  test "$(git hash-object "$ap/$file")" = "$hash"
done < "$s/APRIL.tsv"
while IFS="$t" read -r file repo rev path hash; do
  test "$(git hash-object "$up/$file")" = "$hash"
done < "$s/SUBT.tsv"
test "$(git hash-object "$prior/driver.cpp")" = "123dd5a5c6adf43477e7637f36598a6debf019fd"
for row in "$6/gate.py:2f3efc2d3f147fd36000facf86e8f8ca2258f49f" \
    "$7/release.py:2b3da4f85d129bf1c31cd9d3594c537d5ec5c654" \
    "$8/guard.py:189ed7db9a796f9f083610d9fb3e7ef93c5b1080"
do
  test "$(git hash-object "${row%:*}")" = "${row##*:}"
done
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cc -O2 -std=gnu99 -I"$ap" "$ap/apriltag.c" "$ap/apriltag_quad_thresh.c" "$ap/tag36h11.c" \
   "$ap"/common/*.c "$s/tag.c" -o "$d/tag" -pthread -lm
cp "$up"/subt/* "$d"
(cd "$d" && python3 -B extract.py)
c++ -std=c++17 -Wno-return-type -O2 -I"$d" -I"$prior" "$s/payload.cpp" -o "$d/data"
python3 -B "$s/replay.py" "$d/tag" "$d/data" "$4/spatial.py" "$5" "$6" "$7" "$8"
