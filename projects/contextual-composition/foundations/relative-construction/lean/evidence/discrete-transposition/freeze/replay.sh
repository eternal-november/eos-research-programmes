#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
test "$#" = 2
here=$(cd "$(dirname "$0")" && pwd)
python3 "$here/assemble.py" "$1" "$2"
cd "$2"
source "$here/environment.sh"
mkdir -p .lake evidence
ln -s "$PACKAGES" .lake/packages
test ! -e .lake/build
echo "$(date -u +%FT%T.%NZ) BEGIN clean project build"
lake build 2>&1 | tee evidence/build.log
echo "$(date -u +%FT%T.%NZ) PASS clean project build"
runlean() { lake env lean "$@"; }
source "$here/audit-and-probes.sh"
