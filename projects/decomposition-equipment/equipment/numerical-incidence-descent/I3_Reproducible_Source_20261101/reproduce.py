#!/usr/bin/env python3
"""Check bundle identities and replay the independent finite I3 evidence."""
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def safe_file(relative):
    rel = PurePosixPath(relative)
    require(not rel.is_absolute() and '..' not in rel.parts, 'unsafe manifest path')
    path = ROOT.joinpath(*rel.parts)
    require(path.is_file() and not path.is_symlink(), 'missing or nonregular manifest file: ' + relative)
    return path


def verify_pins(records):
    for record in records:
        path = safe_file(record['path'])
        require(path.stat().st_size == record['bytes'], 'byte-size mismatch: ' + record['path'])
        require(digest(path) == record['sha256'], 'SHA256 mismatch: ' + record['path'])


def main():
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required')
    manifest = json.loads((ROOT / 'MANIFEST_SHA256.json').read_text(encoding='utf-8'))
    verify_pins(manifest['files'])
    expected = {record['path'] for record in manifest['files']} | {'MANIFEST_SHA256.json'}
    observed = {str(path.relative_to(ROOT)) for path in ROOT.rglob('*') if path.is_file()}
    require(observed == expected, 'bundle contains an extra or missing file')
    require(not any(path.is_symlink() for path in ROOT.rglob('*')), 'symlinks are not part of this bundle')
    source_map = json.loads((ROOT / 'source_locator_map.json').read_text(encoding='utf-8'))
    for record in source_map['sources']:
        path = safe_file(record['package_path'])
        require(path.stat().st_size == record['bytes'] and digest(path) == record['sha256'],
                'dependency identity mismatch: ' + record['package_path'])
    for name in ('author_freeze_identity.json', 'review/final_review_pins.json'):
        verify_pins(json.loads((ROOT / name).read_text(encoding='utf-8'))['files'])
    contract = safe_file(source_map['original_contract_package_path']).read_bytes()
    start = contract.index(b'### I3 Objective and numerical incidence quotients')
    stop = contract.index(b'### I4 Cut and substitution interchange', start)
    require(contract[start:stop] == (ROOT / 'I3_Original_Clauses_Verbatim.txt').read_bytes(),
            'original I3 excerpt differs from unchanged contract')
    with tempfile.TemporaryDirectory(prefix='i3-clean-replay-') as temp:
        work = Path(temp)
        for name in ('verify_i3.py', 'run_guards.py'):
            shutil.copyfile(ROOT / 'checks' / name, work / name)
        result = subprocess.run([sys.executable, str(work / 'run_guards.py')], cwd=work,
                                capture_output=True, text=True, timeout=1200)
        require(result.returncode == 0, 'independent finite replay failed: ' + result.stderr)
        for name in ('results.json', 'guard_results.json'):
            require((work / name).read_bytes() == (ROOT / 'checks' / name).read_bytes(),
                    'replay changed expected mathematical evidence: ' + name)
    print(json.dumps({
        'status': 'PASS',
        'manifest_payload_files': len(manifest['files']),
        'exact_dependency_files': len(source_map['sources']),
        'original_I3_excerpt_matches_contract': True,
        'replayed_baseline_modes': 3,
        'rejected_semantic_mutations': 8,
        'mathematical_result_sha256': digest(ROOT / 'checks/results.json'),
        'guard_result_sha256': digest(ROOT / 'checks/guard_results.json'),
        'scope': 'Byte identities and bounded finite replay; not a kernel proof or global acceptance.'
    }, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
