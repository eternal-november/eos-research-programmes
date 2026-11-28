#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
test "$(git hash-object "$UP/geom/cave_circuit_01.dat")" = 5d53ca3aefec299168a1b49f6d2900bf51b42774
test "$(git hash-object "$UP/vis/world.dot")" = f648a8585044dcf16b89e6830ab2bb6337243d4a
test "$(git hash-object "$UP/geom/world.sdf")" = f9f41a9b7e5948f1808adb2397b678272f37833b
cmp "$UP/geom/PINS.txt" "$HERE/COLLISION.sha256"
python3 -B "$HERE/lower.py" "$UP"
python3 -B "$HERE/ride.py" "$UP/geom" "$HERE/site_poses.json"
