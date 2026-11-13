#!/usr/bin/env python3
"""Run normal/-O exact checks, negative controls, parity, and content manifest."""
from hashlib import sha256
from pathlib import Path
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SCRIPT = ROOT / 'exact_checks.py'


def run(options):
    return subprocess.run([sys.executable, *options, str(SCRIPT)],
                          capture_output=True, text=True, check=False)


def main():
    normal = run([])
    optimized = run(['-O'])
    for label, result in [('normal', normal), ('optimized', optimized)]:
        if result.returncode:
            raise RuntimeError(f'{label} checks failed: {result.stderr}')
    if normal.stdout != optimized.stdout:
        raise RuntimeError('normal and optimized outputs differ')
    results = json.loads(normal.stdout)
    (ROOT / 'results.json').write_text(normal.stdout)
    (ROOT / 'results_optimized.json').write_text(optimized.stdout)
    failures = {}
    for label, options in [('normal', []), ('optimized', ['-O'])]:
        result = subprocess.run([sys.executable, *options, str(SCRIPT), '--self-test-failure'],
                                capture_output=True, text=True, check=False)
        if result.returncode != 1 or 'CHECK FAILED: deliberate failure' not in result.stderr:
            raise RuntimeError(f'{label} deliberate failure did not fail as expected')
        failures[label] = {'exit_code': result.returncode, 'stderr': result.stderr.strip()}
    verification = {
        'status': 'PASS', 'python_version': platform.python_version(),
        'normal_exit_code': normal.returncode, 'optimized_exit_code': optimized.returncode,
        'normal_and_optimized_outputs_identical': True,
        'negative_controls': failures,
        'graph_closure_cases': len(results['graph_closures']),
        'fixed_step_interpolation_eta_values': len(results['fixed_step_identities']),
        'native_star_width_cases': len(results['native_width_and_non_descent']['stars']),
        'HMM_prime_family_control_counts': [x['controls'] for x in results['hmm_examples']['prime_family']],
        'diagnostic_counterexample': results['comparative_terminal_effect_gap']['status'],
        'limitations': 'Finite exact checks are not proofs, empirical validation, literature verification, or novelty clearance.'}
    (ROOT / 'verification.json').write_text(json.dumps(verification, indent=2, sort_keys=True) + '\n')
    manifest = {path.name: {'bytes': path.stat().st_size, 'sha256': sha256(path.read_bytes()).hexdigest()}
                for path in sorted(ROOT.iterdir()) if path.is_file() and path.name != 'manifest.json'}
    (ROOT / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps(verification, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
