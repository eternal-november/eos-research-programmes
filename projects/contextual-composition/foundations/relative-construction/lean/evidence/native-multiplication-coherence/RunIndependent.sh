#!/usr/bin/env bash
set -euo pipefail
: "${LEAN_BIN:?absolute bin}" "${REVIEW_PACKAGE:?absolute cold-built directory}"
export PATH="$LEAN_BIN:$PATH"
review="$(cd "$(dirname "$0")" && pwd)"
cd "$REVIEW_PACKAGE"
for f in IndependentProbe IndependentConstraints IndependentHorizontal; do
  echo "$(date -u +%FT%TZ) start $f"
  lake env lean "$review/$f.lean"
  echo "$(date -u +%FT%TZ) PASS $f"
done
