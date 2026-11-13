#!/usr/bin/env python3
"""Replay pinned finite I4 evidence. No external writes; stdout is deterministic JSON."""
import sys
if sys.flags.optimize or not __debug__:
    raise SystemExit('Refusing optimized Python: run without -O/-OO.')
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
pins=json.loads((ROOT/'finite_source_pins.json').read_text())
for name,wanted in pins.items():
    actual=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    if actual!=wanted: raise SystemExit('Source hash mismatch: '+name)
import core_checks
import boundary_quotient_checks
result={
    'status':'PASS',
    'evidence_kind':'Finite C evidence, not an all-degree proof or global I4 acceptance',
    'domain_note':{
        'actual_span_extension':'Explicit finite apex/leg tables in code; not asserted to lie in original discrete C5 graph-span signature.',
        'original_quotient_slice':'Contiguous clique occupancy tables, within-clique permutations; full typed O remains separate.',
        'invertibility_scope':'Evaluated coefficient transformation over a fixed retained occurrence forest; never inverse of forest-bearing arrow.',
        'root':'Same flattened fixed output root, arbitrary endpoint-preserving gamma; recursive exact top edge is separate from root output.',
        'W_scope':'Endpoint-preserving coefficient maps at fixed interfaces after specified pullback; old W only when old arrow is retained.',
        'B_scope':'Separate composite-of-restrictions comparison, all named runs and separate nullary diagonal.',
        'exhaustiveness':'Only expressly listed finite domains; growth samples do not prove all degrees.',
        'determinism':'Standard library; no random inputs; sorted JSON; no timestamps or environment-specific absolute paths.'
    },
    'source_sha256':pins,
    'core':core_checks.run(),
    'boundary_and_cluster':boundary_quotient_checks.run()
}
print(json.dumps(result,sort_keys=True,indent=2))
