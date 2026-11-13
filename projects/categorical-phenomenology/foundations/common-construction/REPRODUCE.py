#!/usr/bin/env python3
"""Repeat its exact finite checks.

This does not compile TeX or mechanically verify the mathematical proofs.
"""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
expected = (root / 'checks' / 'expected_results.json').read_bytes()
for flags in ([], ['-O']):
    output = subprocess.check_output([sys.executable, *flags, str(root / 'checks' / 'verify_boundary.py')], cwd=root)
    if output != expected:
        raise SystemExit('Finite checks differ from expected results')
print('PASS: retained exact finite checks (normal and -O).')
print('TeX is uncompiled; these checks supplement, not replace, the proofs.')
