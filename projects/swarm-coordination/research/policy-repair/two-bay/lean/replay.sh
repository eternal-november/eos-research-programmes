#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?usage: replay.sh /path/to/pinned/lake/project}" && pwd)
mode=${2:-all}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"
cd "$project"
lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
if [[ "$mode" == all ]]; then
  lake build Mathlib.Data.Fintype.BigOperators Mathlib.Data.Fintype.Fin
fi
lake env lean --root="$here" -o "$out/SwarmTwoBayPolicyTables.olean" "$here/SwarmTwoBayPolicyTables.lean"
lake env lean --root="$here" -o "$out/SwarmTwoBayPolicyNormalForm.olean" "$here/SwarmTwoBayPolicyNormalForm.lean"
if [[ "$mode" == all ]]; then
  lake env lean --root="$here" -o "$out/SwarmTwoBayPolicyTableCount.olean" "$here/SwarmTwoBayPolicyTableCount.lean"
fi
