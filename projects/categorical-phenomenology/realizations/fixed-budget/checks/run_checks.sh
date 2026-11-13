#!/usr/bin/env bash
# Run both interpreter modes and compare their exact mathematical reports.
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
python3 run_checks.py --json results_normal.json | tee results_normal.txt
python3 -O run_checks.py --json results_optimized.json | tee results_optimized.txt
python3 - <<'PY'
import json
from pathlib import Path
normal=json.loads(Path('results_normal.json').read_text(encoding='utf-8'))
optimized=json.loads(Path('results_optimized.json').read_text(encoding='utf-8'))
if normal.pop('optimization_level') != 0:
    raise SystemExit('FAIL: ordinary run unexpectedly used optimization')
if optimized.pop('optimization_level') != 1:
    raise SystemExit('FAIL: optimized run did not use optimization level one')
if normal != optimized:
    raise SystemExit('FAIL: normal and optimized mathematical results differ')
print('PASS: normal and optimized mathematical reports match exactly')
PY
