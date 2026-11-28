#!/bin/sh
set -eu
H=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
U=$(CDPATH= cd -- "$1" && pwd)
P=$(CDPATH= cd -- "$2" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
export OPENBLAS_NUM_THREADS=1
while IFS="$(printf '\t')" read -r dest repo rev path sha; do
  test "$(git hash-object "$U/$dest")" = "$sha"
  cp "$U/$dest" "$D/$(basename "$dest")"
done < "$H/SOURCE.tsv"
while IFS="$(printf '\t')" read -r dest repo rev path sha; do
  test "$(git hash-object "$P/$dest")" = "$sha"
done < "$H/PARENT_INPUTS.tsv"
while IFS="$(printf '\t')" read -r dest rev path sha; do
  test "$(git hash-object "$H/$dest")" = "$sha"
done < "$H/ACTUATOR_INPUTS.tsv"
test "$(git hash-object "$U/geom/cave_circuit_01.dat")" = 5d53ca3aefec299168a1b49f6d2900bf51b42774
test "$(git hash-object "$U/geom/world.sdf")" = f9f41a9b7e5948f1808adb2397b678272f37833b
cmp "$U/geom/PINS.txt" "$P/COLLISION.sha256"
cd "$D"
python3 -B "$P/proof.py" "$U" "$P/duals.json" > lower.jsonl
python3 -B "$P/certify_routes.py" "$U/geom" "$P/site_poses.json" "$P/paths.json" lower.jsonl >> lower.jsonl
cmp lower.jsonl "$P/EXPECTED.jsonl"
python3 -B "$P/gate_ray.py" "$U/geom" "$P/site_poses.json" > rays.json
python3 -B "$H/projection.py" "$P/paths.json" rays.json "$P/site_poses.json" "$U/geom/cave_circuit_01.dat" world.dot sites.tsv
PYTHONPATH="$P" python3 -B "$H/bind.py" "$U/geom" "$P/site_poses.json" "$P/paths.json" rays.json sites.tsv
python3 -B extract_radio.py
python3 -B extract_visible.py
python3 -B "$H/extract_extra.py"
g++ -O2 -std=c++17 -Wno-return-type -I . "$H/mission.cpp" -o mission
python3 -B "$H/bridge.py" ./mission sites.tsv
