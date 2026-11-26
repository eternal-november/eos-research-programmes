#!/bin/sh
set -eu
# warehouse, spatial producer, named, in-flight, ptp, clock notification study, shared core
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
for row in "$2/gate.py:2f3efc2d3f147fd36000facf86e8f8ca2258f49f" "$3/release.py:2b3da4f85d129bf1c31cd9d3594c537d5ec5c654" "$4/guard.py:189ed7db9a796f9f083610d9fb3e7ef93c5b1080"
do
  test "$(git hash-object "${row%:*}")" = "${row##*:}"
done
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
python3 -B "$s/spatial.py" "$1" "$2" "$3" "$4" > "$d/space.json"
python3 -B "$s/clock_probe.py" "$5" "$6" > "$d/clock.txt"
python3 -B "$s/replay.py" "$d/space.json" "$d/clock.txt" "$6" "$7"
