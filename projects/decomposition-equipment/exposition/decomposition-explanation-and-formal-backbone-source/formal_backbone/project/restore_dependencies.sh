#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version | grep -q 'version 4.35.0'
# The committed manifest pins every package; do not run lake update to advance it.
BEFORE=$(sha256sum lake-manifest.json | cut -d' ' -f1)
lake exe cache get
AFTER=$(sha256sum lake-manifest.json | cut -d' ' -f1)
[[ "$BEFORE" = "$AFTER" ]] || { echo 'Manifest changed; do not accept this dependency setup' >&2; exit 1; }
python3 - <<'PY'
import json,subprocess
from pathlib import Path
for e in json.loads(Path('lake-manifest.json').read_text())['packages']:
 p=Path('.lake/packages')/e['name']
 actual=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
 if actual!=e['rev']:raise SystemExit('Revision mismatch: '+e['name'])
print('PASS: all dependency revisions match the delivered manifest')
PY
