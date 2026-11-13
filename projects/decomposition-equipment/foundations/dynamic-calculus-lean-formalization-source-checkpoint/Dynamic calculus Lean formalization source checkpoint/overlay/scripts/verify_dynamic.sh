#!/usr/bin/env bash
# Additive focused verification. Original sources and historical evidence are read-only.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null || { echo 'Put pinned Lean/Lake on PATH (workspace: source ../.toolchain/env.sh)' >&2; exit 1; }
OUT="reproduction/dynamic-$(date -u +%Y%m%dT%H%M%S)-$$"
mkdir -p "$OUT"
bash verify_export.sh --manifest-only | tee "$OUT/original-manifest.log"
sha256sum -c INTEGRATION_EXPORT_FILES.sha256 --quiet
echo "PASS: every original integration-export payload hash unchanged" | tee "$OUT/integration-hashes.log"
lake build WitnessedDecompositions.Dynamic.Bridge | tee "$OUT/build.log"
lake env lean audit/DynamicAxiomAudit.lean | tee "$OUT/axioms.log"
python3 - "$OUT/axioms.log" <<'PY'
import pathlib, re, sys
report = pathlib.Path(sys.argv[1]).read_text()
audit = pathlib.Path('audit/DynamicAxiomAudit.lean').read_text()
expected = len(re.findall(r'^#print axioms\b', audit, re.M))
closures = re.findall(r'depends on axioms:\s*\[([^]]*)\]', report, re.S)
empty = len(re.findall(r'does not depend on any axioms', report))
if expected != len(closures) + empty:
    raise SystemExit('Incomplete axiom report')
seen = {a.strip() for c in closures for a in c.split(',') if a.strip()}
extra = seen - {'propext', 'Quot.sound', 'Classical.choice'}
if extra:
    raise SystemExit(f'Unexpected axioms: {sorted(extra)}')
print(f'PASS: {expected} headline axiom closures; only standard Lean axioms')
PY
# Mandatory fresh-project compile, independent regressions and rejection controls.
# This shares only the pinned external dependency cache, never project oleans.
python3 audit/dynamic_independent/verify_fresh.py | tee "$OUT/independent-fresh.log"
printf 'PASS: focused dynamic target verification; logs in %s\n' "$OUT"
