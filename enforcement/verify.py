"""Reproduce the fallible-enforcement package and bind results to exact sources.

Use --check for verification. --write is an explicit evidence refresh after review.
The checker never alters research sources, Git state or the primary checkout.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
SOURCES = (
    '../MOTIVATING-PROBLEM.md', '../ENFORCEMENT-CONTRACT.md', '../ENFORCEMENT-SOURCES.md',
    '../handoff/EXECUTION.md', 'THEORY.md', 'BRAKE-PROOFS.md', 'BOUNDARIES.md', 'FINITE.md',
    'Brakes.lean', 'brake_checks.py', 'boundary_checks.py', 'boundary_results.json',
    'finite_model.py', 'finite_results.json', 'verify.py',
)


def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)


def normalized(data):
    return data.replace(b'\r\n', b'\n')


def fingerprints():
    return {name: hashlib.sha256(normalized((HERE / name).read_bytes())).hexdigest()
            for name in SOURCES}


def run(args, input_text=None):
    result = subprocess.run(args, cwd=HERE, input=input_text, capture_output=True, text=True, encoding='utf-8')
    require(result.returncode == 0,
            'Check failed: ' + repr(args) + '\n' + result.stdout + '\n' + result.stderr)
    require(not result.stderr.strip(), 'Unexpected stderr from check: ' + result.stderr)
    return result.stdout.replace('\r\n', '\n').strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    parser.add_argument('--lean', default=str(Path(os.environ['USERPROFILE']) / '.elan' / 'toolchains' /
                                             'leanprover--lean4---v4.33.0' / 'bin' / 'lean.exe'))
    args = parser.parse_args()
    require(sys.flags.optimize == 0, 'Run without Python optimization; executable checks must remain active')
    require(sys.version_info[:2] == (3, 12), 'This reproduction record pins Python 3.12')
    before = fingerprints()
    record_path = HERE / 'verification.json'
    expected = None
    if args.check:
        expected = json.loads(record_path.read_text(encoding='utf-8'))
        require(expected['sources_sha256_lf'] == before, 'Source fingerprints differ; review changes before refreshing evidence')
    lean_version = run([args.lean, '--version'])
    require('version 4.33.0,' in lean_version, 'Lean 4.33.0 required')
    print('Checking Lean statements and axiom dependencies...', flush=True)
    lean_source = (HERE / 'Brakes.lean').read_text(encoding='utf-8')
    names = re.findall(r'^theorem ([A-Za-z0-9_]+)', lean_source, re.MULTILINE)
    require(len(names) == 26, 'Expected 26 theorem declarations')
    extra = '\n'.join('#print axioms ByzantineEnforcement.' + name for name in names)
    lean_output = run([args.lean, '--stdin'], lean_source + '\n' + extra + '\n')
    reports = sorted(set(line for line in lean_output.splitlines() if 'axioms' in line))
    require(len(reports) == 26, 'Expected all 26 theorem axiom reports')
    require(all('sorryAx' not in line for line in reports), 'Admitted theorem detected')
    allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    for line in reports:
        if 'does not depend on any axioms' in line:
            continue
        match = re.search(r'depends on axioms: \[(.*)\]$', line)
        require(match is not None, 'Unrecognized Lean axiom report')
        dependencies = {item.strip() for item in match.group(1).split(',') if item.strip()}
        require(dependencies <= allowed_axioms, 'Unexpected Lean axiom dependencies: ' + repr(dependencies))
    require('sorry' not in lean_output.lower() and 'warning' not in lean_output.lower(), 'Unexpected Lean diagnostic')
    print('Checking exact margins and boundary witnesses...', flush=True)
    brake_output = json.loads(run([sys.executable, '-B', str(HERE / 'brake_checks.py')]))
    boundary_output = json.loads(run([sys.executable, '-B', str(HERE / 'boundary_checks.py')]))
    print('Reproducing exhaustive finite synthesis and composition checks...', flush=True)
    finite_output = run([sys.executable, '-B', str(HERE / 'finite_model.py'), '--check'])
    finite = json.loads((HERE / 'finite_results.json').read_text(encoding='utf-8'))
    require(finite['positive']['winning'], 'Positive finite result is not winning')
    require(finite['bounded_synthesis']['examined'] == 64, 'Bounded table coverage changed')
    after = fingerprints()
    require(before == after, 'Research source changed during checking')
    actual = {
        'format': 1, 'scope': 'Discrete model proofs, exact witnesses and finite bounded synthesis; no hardware validation',
        'sources_sha256_lf': before, 'lean_version': lean_version,
        'python_major_minor': list(sys.version_info[:2]), 'lean_axiom_reports': reports,
        'exact_brake_results': brake_output, 'exact_boundary_results': boundary_output,
        'finite_checker_output': finite_output,
        'finite_positive_states': finite['positive']['explored_states'],
        'finite_positive_edges': finite['positive']['checked_edges'],
        'finite_memoryless_winners': len(finite['bounded_synthesis']['winners']),
    }
    rendered = json.dumps(actual, indent=2, sort_keys=True) + '\n'
    if args.write:
        record_path.write_text(rendered, encoding='utf-8', newline='\n')
        print('PASS: fresh evidence written to ' + str(record_path), flush=True)
    else:
        require(expected == actual, 'Recorded evidence differs from fresh reproduction')
        print('PASS: all bound evidence reproduced', flush=True)


if __name__ == '__main__':
    main()
