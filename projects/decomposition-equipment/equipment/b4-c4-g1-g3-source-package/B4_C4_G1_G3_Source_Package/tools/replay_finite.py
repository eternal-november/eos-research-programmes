#!/usr/bin/env python3
"""Replay bounded checks in a temporary copy, preserving frozen evidence."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
if not __debug__:
    raise SystemExit('Run this wrapper without -O or -OO')

CASES = [
    ('b4/checks/verify_b4.py', 'b4/checks/result.json', {'elapsed_seconds', 'python_optimization'}),
    ('c4/checks/verify_c4.py', 'c4/checks/results.json', set()),
    ('c4/audit/independent_c4/independent_falsification.py', 'c4/audit/independent_c4/independent_falsification_results.json', set()),
    ('g/verify_g_observation_recovery.py', 'g/G_finite_results.json', set()),
    ('review/independent_recovery_checks.py', 'review/independent_recovery_results.json', set()),
]
results = []
with tempfile.TemporaryDirectory(prefix='b4_c4_g_replay_') as td:
    work = Path(td)
    for script, reference, ignored in CASES:
        p = work / script
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / script, p)
        done = subprocess.run([sys.executable, str(p)], cwd=work, text=True, capture_output=True)
        if done.returncode:
            raise RuntimeError(script + ' failed:\n' + done.stdout + done.stderr)
        got = json.loads(done.stdout)
        want = json.loads((ROOT / reference).read_text())
        if got.get('status') != 'PASS':
            raise RuntimeError(script + ': non-PASS receipt')
        if {k:v for k,v in got.items() if k not in ignored} != {k:v for k,v in want.items() if k not in ignored}:
            raise RuntimeError(script + ': semantic receipt mismatch')
        results.append({'script': script, 'status': 'PASS', 'reference': reference, 'comparison': 'all fields except ' + ', '.join(sorted(ignored)) if ignored else 'exact JSON fields'})
    for script, reference, ignored in CASES[:3]:
        for mode in (('-O', '-OO') if script.startswith('b4/') else ('-O',)):
            done = subprocess.run([sys.executable, mode, str(work / script)], cwd=work, text=True, capture_output=True)
            if done.returncode:
                raise RuntimeError(script + ': optimized explicit checks failed')
            got = json.loads(done.stdout)
            want = json.loads((ROOT / reference).read_text())
            if {k:v for k,v in got.items() if k not in ignored} != {k:v for k,v in want.items() if k not in ignored}:
                raise RuntimeError(script + ': optimized receipt mismatch')
            results.append({'script': script, 'mode': mode, 'status': 'PASS'})
    shutil.copytree(ROOT / 'b4/formal', work / 'b4/formal')
    guards = subprocess.run([sys.executable, str(work / 'b4/formal/test_runner_guards.py')], cwd=work, text=True, capture_output=True)
    if guards.returncode or json.loads(guards.stdout) != json.loads((ROOT / 'b4/formal/guard_results.json').read_text()):
        raise RuntimeError('Frozen-source guard replay mismatch: ' + guards.stdout + guards.stderr)
    results.append({'script': 'b4/formal/test_runner_guards.py', 'status': 'PASS', 'scope': 'no Lean compilation; altered-source and stale-PASS rejection normal/-O/-OO'})
    for script in ('g/verify_g_observation_recovery.py', 'review/independent_recovery_checks.py'):
        done = subprocess.run([sys.executable, '-O', str(work / script)], cwd=work, text=True, capture_output=True)
        if done.returncode == 0:
            raise RuntimeError(script + ': optimized assertions unexpectedly accepted')
        results.append({'script': script, 'mode': '-O', 'status': 'EXPECTED_REJECTION'})
print(json.dumps({'status': 'PASS', 'scope': 'bounded finite replay only; no unrestricted theorem or new Lean check', 'checks': results}, indent=2))
