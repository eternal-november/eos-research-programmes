#!/bin/sh
set -eu
H=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
U=$(CDPATH= cd -- "$1" && pwd)
P=$(CDPATH= cd -- "$2" && pwd)
B=$(CDPATH= cd -- "$3" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
export OPENBLAS_NUM_THREADS=1
check() {
  while IFS="$(printf '\t')" read -r dest repo rev path sha; do
    test "$(git hash-object "$1/$dest")" = "$sha"
    if [ "$3" = copy ]; then cp "$1/$dest" "$D/$(basename "$dest")"; fi
  done < "$2"
}
check "$B" "$H/BASE_INPUTS.tsv" nocopy
check "$U" "$B/SOURCE.tsv" copy
check "$P" "$B/PARENT_INPUTS.tsv" nocopy
test "$(git hash-object "$U/geom/cave_circuit_01.dat")" = 5d53ca3aefec299168a1b49f6d2900bf51b42774
test "$(git hash-object "$U/geom/world.sdf")" = f9f41a9b7e5948f1808adb2397b678272f37833b
cmp "$U/geom/PINS.txt" "$P/COLLISION.sha256"
cd "$D"
python3 -B "$P/gate_ray.py" "$U/geom" "$P/site_poses.json" > rays.json
python3 -B "$B/projection.py" "$P/paths.json" rays.json "$P/site_poses.json" "$U/geom/cave_circuit_01.dat" world.dot sites.tsv
PYTHONPATH="$P" python3 -B "$B/bind.py" "$U/geom" "$P/site_poses.json" "$P/paths.json" rays.json sites.tsv > binding.json
printf "%s\n" '{"hit_segments": [[[4], []], [[], [5]]], "route_requiring_gate": [0, 1]}' | cmp - binding.json
python3 -B extract_radio.py
python3 -B extract_visible.py
python3 -B "$B/extract_extra.py"
cp "$B/mission.cpp" .
patch -s mission.cpp "$H/mission.patch"
g++ -O2 -std=c++17 -Wno-return-type mission.cpp -o mission
python3 -B "$H/bridge.py" ./mission sites.tsv
