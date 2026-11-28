#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
    test "$(git hash-object "$UP/$dest")" = "$sha"
    cp "$UP/$dest" "$D/$(basename "$dest")"
done < "$HERE/SOURCE.tsv"
cd "$D"
python3 -B extract_radio.py
python3 -B extract_visible.py
test "$(git hash-object "$UP/geom/cave_circuit_01.dat")" = 5d53ca3aefec299168a1b49f6d2900bf51b42774
test "$(git hash-object "$UP/geom/world.sdf")" = f9f41a9b7e5948f1808adb2397b678272f37833b
test "$(git hash-object "$UP/vis/world.sdf")" = "$(git hash-object "$UP/geom/world.sdf")"
cmp "$UP/geom/PINS.txt" "$HERE/COLLISION.sha256"
python3 -B "$HERE/survey.py" "$UP/geom" > "$D/poses.json"
python3 -B "$HERE/gate_ray.py" "$UP/geom" "$HERE/site_poses.json" > "$D/rays.json"
cat "$D/rays.json"
python3 -B "$HERE/project.py" "$D/poses.json" "$UP/geom/cave_circuit_01.dat" "$D/rays.json"
g++ -std=c++17 -O2 -Wno-return-type -I "$D" "$HERE/native_routes.cpp" -o "$D/route"
"$D/route" "$D/sites.tsv"
