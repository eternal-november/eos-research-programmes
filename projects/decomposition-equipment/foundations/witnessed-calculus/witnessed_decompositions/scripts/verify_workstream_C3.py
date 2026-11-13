#!/usr/bin/env python3
"""Fresh C3 checkpoint reproduction; P/X review is a separate acceptance gate.

Requires only Python standard library plus inherited pinned Lean/Lake packages.
No project proof objects are reused by the inherited verification chain.
"""
from pathlib import Path
import datetime
import hashlib
import importlib.util
import json
import subprocess
import sys
import traceback

ROOT = Path(__file__).resolve().parents[1]
C = ROOT / 'research/workstream_C3'
CONTRACT = '47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET = '88ea710752d99cd83d10c85740f825b1c543d58c0f475615c667020bc1aa2825'


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def invariants():
    baseline = json.loads((C / 'BaselinePreservation.json').read_text())
    assert baseline['count'] == len(baseline['files']) == 578
    for row in baseline['files']:
        assert digest(ROOT / row['path']) == row['sha256'], row['path']
    assert digest(ROOT / 'research/CompletionContract.md') == CONTRACT
    assert digest(C / 'C3_Targets.md') == TARGET
    for line in (C / 'C3_SourceSnapshot.sha256').read_text().splitlines():
        expected, rel = line.split('  ', 1)
        assert digest(ROOT / rel) == expected, rel
    print('578 baseline files, contract, target and C3 source snapshot PASS', flush=True)


def run(command, logfile):
    with logfile.open('w') as stream:
        proc = subprocess.run([str(x) for x in command], cwd=ROOT,
                              stdout=stream, stderr=subprocess.STDOUT)
    assert proc.returncode == 0, f'{command}: see {logfile}'


def stable(x):
    if isinstance(x, dict):
        return {k: stable(v) for k, v in x.items() if k not in {'python', 'python_version'}}
    if isinstance(x, list):
        return [stable(v) for v in x]
    return x


def compare(p, q):
    assert stable(json.loads(p.read_text())) == stable(json.loads(q.read_text())), (p, q)


def main():
    out = ROOT / 'reproduction_C3' / datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out.mkdir(parents=True)
    report = {'status': 'RUNNING', 'contract_sha256': CONTRACT,
              'target_sha256': TARGET, 'reproduction_dir': str(out.relative_to(ROOT)),
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        invariants()
        run(['bash', 'verify_workstream_C2.sh'], out / 'inherited-ABC1C2-full.log')
        run([sys.executable, C / 'finite/check_c3.py', '--output', out / 'author.json'],
            out / 'author.log')
        compare(out / 'author.json', C / 'finite/AuthorCertificate.json')
        run([sys.executable, C / 'review/IndependentFinite.py', '--root', ROOT,
             '--output', out / 'independent.json'], out / 'independent.log')
        compare(out / 'independent.json', C / 'review/IndependentFinite.json')
        a = json.loads((out / 'author.json').read_text())
        i = json.loads((out / 'independent.json').read_text())
        assert a['status'] == i['status'] == 'PASS'
        invariants()
        report.update(status='PASS', baseline_files_unchanged=578,
                      source_snapshot_sha256=digest(C / 'C3_SourceSnapshot.sha256'),
                      author_certificate_sha256=digest(out / 'author.json'),
                      independent_certificate_sha256=digest(out / 'independent.json'),
                      inherited='Complete unchanged A/B/C1/C2 verification with fresh project Lean objects',
                      c3='All frozen author/independent finite domains and executed negative controls reproduced',
                      assurance='C3 P/X proofs remain separately non-author-reviewed; no new Lean claim',
                      scope='C3 only; no other obligation status changed or workstream activated')
    except BaseException as exc:
        report.update(status='FAIL', error=repr(exc))
        traceback.print_exc()
    finally:
        report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=2), flush=True)
    return 0 if report['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
