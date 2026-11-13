#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
OLD="${E1_ORIGINAL_SOURCE:-$ROOT/original_source}"
CACHE="${E1_UPSTREAM_PROJECT:-/workspace/shared/d1_equivariant_transport_20261031/formal/toolchain/project}"
DEST="${1:?Supply a new, absent project directory}"
[[ ! -e "$DEST" ]] || { echo 'Fresh destination must not already exist' >&2; exit 1; }
mkdir -p "$DEST/research/workstream_C2/lean" "$DEST/.lake/packages"
cp "$OLD"/{lakefile.toml,lake-manifest.json,lean-toolchain,WitnessedDecompositions.lean} "$DEST/"
cp -r "$OLD/WitnessedDecompositions" "$DEST/"
find "$DEST/WitnessedDecompositions" -type f ! -name '*.lean' -delete
cp "$OLD/research/workstream_C2/lean/RelationInterface.lean" "$DEST/research/workstream_C2/lean/"
while IFS= read -r name; do
  ln -s "$CACHE/.lake/packages/$name" "$DEST/.lake/packages/$name"
done < <(python3 -c 'import json,sys; print("\n".join(p["name"] for p in json.load(open(sys.argv[1]))["packages"]))' "$OLD/lake-manifest.json")
