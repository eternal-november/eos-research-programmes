#!/usr/bin/env python3
"""Verify reproducible reproduce the finite exact-arithmetic checks.

Does not solve the existential-real problem or mechanically verify proofs.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
expected = (root / 'checks' / 'expected_results.json').read_bytes()
with tempfile.TemporaryDirectory(prefix='native-refinement-check-') as temp:
    script = Path(temp) / 'verify_partition_refinements.py'
    shutil.copyfile(root / 'checks' / script.name, script)
    for flags in ([], ['-O']):
        result = subprocess.run([sys.executable, *flags, str(script)], cwd=temp, capture_output=True, check=True)
        if result.stdout != expected or result.stderr:
            raise SystemExit('Finite checks differ from expected results')
print('PASS: reproducible clean-copy normal/-O exact checks.')
print('TeX is uncompiled. General claims rely on the written proofs.')
