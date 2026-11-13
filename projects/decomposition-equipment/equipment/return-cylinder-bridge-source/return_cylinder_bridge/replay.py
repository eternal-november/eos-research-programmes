#!/usr/bin/env python3
"""Verify packaged sources and reproduce pinned finite results offline."""
from pathlib import Path
import hashlib
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    lines = (HERE / 'MANIFEST.sha256').read_text(encoding='utf-8').splitlines()
    seen = set()
    for line in lines:
        expected, relative = line.split('  ', 1)
        path = HERE / relative
        assert relative not in seen, f'duplicate manifest entry: {relative}'
        assert not Path(relative).is_absolute() and '..' not in Path(relative).parts
        assert path.is_file(), f'missing packaged file: {relative}'
        assert digest(path) == expected, f'checksum mismatch: {relative}'
        seen.add(relative)
    print(f'PASS: {len(seen)} packaged-file SHA-256 checks', flush=True)


def run(name):
    env = dict(os.environ)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    subprocess.run([sys.executable, str(HERE / 'scripts' / name)],
                   cwd=HERE, env=env, check=True)


def main():
    check_manifest()
    pairs = [('verify_priority_cylinder.py', 'verification_results.json'),
             ('verify_observable_enrichment.py', 'observable_enrichment_results.json')]
    for script, output in pairs:
        run(script)
        actual = HERE / 'scripts' / output
        expected = HERE / 'reference_results' / output
        assert actual.read_bytes() == expected.read_bytes(), f'result differs: {output}'
        print(f'PASS: byte-identical replay of {output} ({digest(actual)})', flush=True)
    run('verify_observable_decoder_isolation.py')
    print('PASS: complete offline replay; all assertions and result comparisons passed.')


if __name__ == '__main__':
    main()
