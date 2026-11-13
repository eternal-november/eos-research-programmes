#!/usr/bin/env python3
"""Verify deterministic replay, optimized execution and detected negative controls.

Runs scripts only from this directory or a temporary private copy. No network,
inherited package mutation, remote writes, or optional Python dependencies.
"""
import ast
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
PINS = json.loads((ROOT / 'source_pins.json').read_text())


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def invoke(args=(), optimization=None, cwd=ROOT):
    command = [sys.executable]
    if optimization:
        command.append(optimization)
    command += [str(cwd / 'run_checks.py'), *args]
    env = dict(os.environ)
    env.pop('PYTHONOPTIMIZE', None)
    env['PYTHONHASHSEED'] = '0'
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True, env=env)


for name, expected in sorted(PINS.items()):
    data = (ROOT / name).read_bytes()
    require(hashlib.sha256(data).hexdigest() == expected, 'Replay source hash mismatch: ' + name)
    tree = ast.parse(data, filename=name)
    require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)), 'assert forbidden: ' + name)

baseline = invoke()
require(baseline.returncode == 0, baseline.stderr)
require(json.loads(baseline.stdout)['status'] == 'PASS', 'baseline status')
duplicates = {}
for label, opt in [('normal_repeat', None), ('optimized_O', '-O'), ('optimized_OO', '-OO')]:
    result = invoke(optimization=opt)
    require(result.returncode == 0, label + ' failed: ' + result.stderr)
    require(result.stdout == baseline.stdout, label + ' differs from baseline')
    duplicates[label] = 'byte-identical PASS'

mutations = {
    'omit_empty_exceptions': 'uniform path criterion with empty exceptions',
    'ignore_internal_image': 'feasible witness image criterion',
    'existence_is_bijection': 'span unique-lift criterion',
    'merge_occurrence_tuples': 'distinct full original-slot arrows must survive equal totals',
    'erase_groupoid_arrows': 'alias comparison hom bijection retains actual h and full tuple',
    'discard_seam_certificates': 'iso-comma retains two distinct seam certificates and their actual arrows',
    'independent_orbits_are_congruence': 'independent operation orbits do not respect substitution',
}
detected = []
for mutation, expected_message in mutations.items():
    modes = []
    for label, opt in [('normal', None), ('optimized_O', '-O')]:
        result = invoke(('--mutate', mutation), optimization=opt)
        require(result.returncode != 0 and ('RuntimeError: ' + expected_message) in result.stderr,
                mutation + ' was not rejected at the intended guard: ' + result.stderr)
        modes.append(label)
    detected.append({'mutation': mutation, 'rejected_under': modes, 'guard': expected_message})

with tempfile.TemporaryDirectory(prefix='d2_d3_hash_probe_') as tmp:
    copy = Path(tmp)
    for name in (*PINS, 'source_pins.json'):
        shutil.copyfile(ROOT / name, copy / name)
    with (copy / 'd2_finite_checks.py').open('a') as stream:
        stream.write('\n# Deliberate copy-only hash mutation; original is untouched.\n')
    probe = invoke(cwd=copy)
    require(probe.returncode != 0 and 'Source hash mismatch: d2_finite_checks.py' in probe.stderr,
            'tampered private copy not rejected')

print(json.dumps({
    'status': 'PASS',
    'scope': 'Bounded evidence validation, not an acceptance verdict on the mathematical contract',
    'source_sha256': PINS,
    'baseline_output_sha256': hashlib.sha256(baseline.stdout.encode()).hexdigest(),
    'baseline_bytes': len(baseline.stdout.encode()),
    'replay_comparisons': duplicates,
    'no_assert_AST_check': True,
    'mutation_controls': detected,
    'source_tamper_control': 'PASS: changed private copy rejected before imports/tests',
}, sort_keys=True, indent=2))
