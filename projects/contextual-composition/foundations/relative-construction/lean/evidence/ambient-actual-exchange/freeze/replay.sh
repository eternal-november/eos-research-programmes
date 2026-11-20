#!/bin/bash
set -euo pipefail
test "$#" = 2
: "${LEAN_BIN:?path to pinned Lean bin directory}" "${PACKAGES:?absolute path to pinned checked-out dependencies}"
here=$(cd "$(dirname "$0")" && pwd)
python3 "$here/assemble.py" "$1" "$2"; cd "$2"; mkdir -p .lake evidence; ln -s "$PACKAGES" .lake/packages
unset LEAN_PATH LEAN_SRC_PATH; export PATH="$LEAN_BIN:$PATH"
lean --version|grep eb6cafb7290e8bd5f2937522d8d804f58f02bafc
python3 - <<'PY'
import json,subprocess
from pathlib import Path
for p in json.load(open('lake-manifest.json'))['packages']:
 assert subprocess.check_output(['git','-C',str(Path('.lake/packages')/p['name']),'rev-parse','HEAD'],text=True).strip()==p['rev'],p['name']
PY
lake build 2>&1 |tee evidence/build.log
lake env lean AxiomAudit.lean > evidence/axioms.log
python3 audit.py
for f in checks/*.lean;do lake env lean "$f";done
