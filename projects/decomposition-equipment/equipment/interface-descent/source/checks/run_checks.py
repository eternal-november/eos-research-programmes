#!/usr/bin/env python3
"""Pinned deterministic finite evidence. Safe under python -O and -OO."""
import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
PINS = json.loads((ROOT / 'source_pins.json').read_text())
for name, expected in sorted(PINS.items()):
    actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit('Source hash mismatch: ' + name)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--mutate', choices=(
    'omit_empty_exceptions', 'ignore_internal_image', 'existence_is_bijection',
    'merge_occurrence_tuples', 'erase_groupoid_arrows',
    'discard_seam_certificates', 'independent_orbits_are_congruence'))
args = parser.parse_args()

import d2_finite_checks
import d3_finite_checks

if args.mutate:
    if args.mutate in ('omit_empty_exceptions', 'ignore_internal_image', 'existence_is_bijection'):
        d2_finite_checks.run(args.mutate)
    else:
        d3_finite_checks.run(args.mutate)
    raise SystemExit('ERROR: injected mutation survived all controls: ' + args.mutate)

result = {
    'status': 'PASS',
    'evidence_level': 'Bounded executable C evidence; not a Lean proof or original-floor acceptance verdict',
    'source_sha256': PINS,
    'optimization_policy': 'Explicit require guards, no assert statements; normal/-O/-OO outputs compared by replay.py',
    'scope': {
        'D2': 'Independent finite Rel/path enumeration and actual span comparison fibers; bounded ordered-tree examples',
        'D3': 'Original C5 flat-model data via inherited presented/flat isomorphism; actual graph, grade and original-slot tuples',
        'inherited': 'Presentation completeness and arbitrary-tree theorems are mathematical inputs, not proved by these tests',
        'determinism': 'No random choices, timestamps, external dependencies or environment-specific paths in output',
    },
    'D2': d2_finite_checks.run(),
    'D3': d3_finite_checks.run(),
}
print(json.dumps(result, sort_keys=True, indent=2))
