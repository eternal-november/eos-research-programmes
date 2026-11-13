#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
PROJECT="${D1_ORIGINAL_PROJECT:-$ROOT/toolchain/project}"
LEAN="${LEAN:-$(command -v lean || true)}"
if [[ -z "$LEAN" ]]; then LEAN="$ROOT/toolchain/lean-4.35.0-linux/bin/lean"; fi
export PATH="$(dirname "$LEAN"):$PATH"
"$LEAN" --root="$ROOT" -o "$ROOT/D1FiniteTypedAction.olean" "$ROOT/D1FiniteTypedAction.lean" > "$ROOT/build.log" 2>&1
cd "$PROJECT"
lake build WitnessedDecompositions WitnessedDecompositions.RefinementFunctoriality > "$ROOT/original_baseline_replay.log" 2>&1
mkdir -p .lake/build/lib/lean/research/workstream_C2/lean
lake env lean -o .lake/build/lib/lean/research/workstream_C2/lean/RelationInterface.olean research/workstream_C2/lean/RelationInterface.lean > "$ROOT/original_relation_replay.log" 2>&1
LEAN_PATH="$ROOT${LEAN_PATH:+:$LEAN_PATH}" lake env lean "$ROOT/D1OriginalAPIBridge.lean" > "$ROOT/original_api_build.log" 2>&1
if grep -Eq 'sorryAx|Classical.choice' "$ROOT/original_api_build.log"; then
  echo 'Unexpected principal declaration axiom dependency'; exit 1
fi
echo 'D1 original Signature/Assignment/path bridge PASS.'
