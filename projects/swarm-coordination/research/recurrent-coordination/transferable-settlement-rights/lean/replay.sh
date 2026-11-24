#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?usage: replay.sh /path/to/pinned/lake/project}" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "$project"
version=$(lake env lean --version)
printf '%s\n' "$version"
[[ "$version" == *"eb6cafb7290e8bd5f2937522d8d804f58f02bafc"* ]]
revision=$(git -C .lake/packages/mathlib rev-parse HEAD)
printf '%s\n' "$revision"
[[ "$revision" == "56a005855ea17e0b0958f73ec801ae140b0a1679" ]]
lake env lean --root="$here" -o "$out/SettlementRights.olean" "$here/SettlementRights.lean" \
  | tee "$out/axioms.log"
! grep -q 'sorryAx' "$out/axioms.log"
[[ $(grep -c "^'SwarmSettlement\." "$out/axioms.log") -eq 17 ]]
