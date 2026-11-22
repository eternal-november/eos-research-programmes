#!/usr/bin/env bash
# Lean 4.35.0; only Init is imported. No mathlib cache/build required.
set -euo pipefail
cd "$(dirname "$0")/.."
lean --version | grep -F eb6cafb7290e8bd5f2937522d8d804f58f02bafc
temp=$(mktemp -d)
trap 'rm -rf -- "$temp"' EXIT
mkdir -p "$temp/ContextualComposition"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.35.0
lean -o "$temp/ContextualComposition/OppositeTypeFamilies.olean" ContextualComposition/OppositeTypeFamilies.lean
export LEAN_PATH="$temp${LEAN_PATH:+:$LEAN_PATH}"
lean checks/OppositeTypeFamilies.lean
{ echo 'import ContextualComposition.OppositeTypeFamilies'; grep '^#print axioms ContextualComposition.OppositeTypeFamilies\.' AxiomAudit.lean; } > "$temp/Audit.lean"
lean "$temp/Audit.lean"
