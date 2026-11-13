#!/usr/bin/env python3
"""Verify reproducible rerun the exact finite checks from a clean copy."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
expected = (root / 'checks' / 'expected_results.json').read_bytes()
with tempfile.TemporaryDirectory(prefix='native-common-package-') as directory:
    temp = Path(directory)
    for name in ('verify.py', 'expected_results.json'):
        shutil.copyfile(root / 'checks' / name, temp / name)
    for flags in ([], ['-O']):
        result = subprocess.run([sys.executable, *flags, str(temp / 'verify.py')], cwd=temp, capture_output=True, check=True)
        if result.stdout != expected or result.stderr:
            raise SystemExit('Unexpected finite-check output')
print('PASS: reproducible clean-copy normal/-O finite checks.')
print('TeX is uncompiled; finite checks supplement the written proofs.')
