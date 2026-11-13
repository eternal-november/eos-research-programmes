#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LEAN="${LEAN:-$PWD/toolchain/lean-4.35.0-linux/bin/lean}"
"$LEAN" --version
"$LEAN" D1FiniteTypedAction.lean > build.log 2>&1
if grep -Eq 'sorryAx|Classical.choice' build.log; then
  echo 'Unexpected axiom dependency'; exit 1
fi
python test_d1_finite.py > finite.log
python -O test_d1_finite.py > finite_optimized.log
python verify_mutation.py "$LEAN"
echo 'D1 finite representative: Lean and finite checks PASS.'
