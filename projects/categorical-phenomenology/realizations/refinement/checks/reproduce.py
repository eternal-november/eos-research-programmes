#!/usr/bin/env python3
"""Reproduce expected output from a clean source-only temporary directory."""
from pathlib import Path
import tempfile, shutil, subprocess, hashlib, json, sys
base=Path(__file__).resolve().parent
expected=(base/'expected_results.json').read_bytes()
source=base/'verify_partition_refinements.py'
before=source.read_bytes()
with tempfile.TemporaryDirectory(prefix='native-refinement-clean-') as temp:
    path=Path(temp)/source.name
    shutil.copy2(source,path)
    results={}
    for mode, flags in [('normal', []),('optimized', ['-O'])]:
        run=subprocess.run([sys.executable,*flags,str(path)],cwd=temp,capture_output=True,check=True)
        if run.stdout!=expected or run.stderr:
            raise RuntimeError('clean reproduction mismatch: '+mode)
        results[mode]='pass; byte-identical expected JSON; no stderr'
if source.read_bytes()!=before:
    raise RuntimeError('source modified during reproduction')
receipt={'python':sys.version.split()[0], 'clean_copy':results,
'source_sha256':hashlib.sha256(before).hexdigest(),
'expected_output_sha256':hashlib.sha256(expected).hexdigest(),
'cases':json.loads(expected)['totals'],
'polytope_bridge_positive_certificates':json.loads(expected)['polytope_bridge_positive_certificates'],
'scope':'Execution reproducibility only; not formal theorem verification.'}
(base/'reproduction_receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(receipt,indent=2))
