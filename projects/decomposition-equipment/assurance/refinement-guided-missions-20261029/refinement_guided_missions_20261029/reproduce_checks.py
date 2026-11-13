"""Reproduce exact checks and frozen-result summaries, never a timed solver sweep."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def run(args, cwd):
    p = subprocess.run([sys.executable, *args], cwd=cwd, text=True,
                       capture_output=True, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    if p.returncode:
        raise RuntimeError(f'{args} failed:\n{p.stdout}\n{p.stderr}')
    return p.stdout

def read(path):
    return json.loads(path.read_text())

def equal(actual, expected, label):
    assert actual == expected, f'{label}: regenerated content differs'
    print(f'PASS: {label}', flush=True)

with tempfile.TemporaryDirectory(prefix='refinement-replay-') as tmp:
    root = Path(tmp) / 'study'
    shutil.copytree(ROOT, root, ignore=shutil.ignore_patterns('__pycache__', '.venv'))
    run(['verify_manifest.py'], root)
    print('PASS: frozen manifest', flush=True)
    config = read(root / 'example/FROZEN_CONFIGURATION.json')
    raw = read(root / 'example/final_results.json')
    for name, expected in config['source_hashes'].items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == expected
    assert raw['source_sha256'] is None  # composite did not arise from a single source revision
    source_digests = {hashlib.sha256((root / p).read_bytes()).hexdigest()
                      for p in ('example/delayed_missions.py', 'example/v1/delayed_missions.py')}
    assert set(raw['source_sha256_by_method'].values()) <= source_digests
    for row in raw['results']:
        assert row['source_sha256'] == raw['source_sha256_by_method'][row['method']]
    assert raw['protocol_sha256'] == config['source_hashes']['example/FROZEN_PROTOCOL.md']
    expected = {(n,L,s,seed,regime,method) for n,L,s in config['dimensions_n_L_s']
                for seed in config['seeds'] for regime in config['regimes']
                for method in config['methods']}
    actual = [(r['n'],r['L'],r['s'],r['seed'],r['regime'],r['method']) for r in raw['results']]
    assert len(actual) == len(expected) == config['expected_streams'] and set(actual) == expected
    assert all([b['index'] for b in r['batches']] == list(range(config['batches_per_stream']))
               for r in raw['results'])
    assert sum(len(r['batches']) for r in raw['results']) == config['expected_method_batch_records']
    print('PASS: source/protocol hashes and complete prescribed suite coverage', flush=True)
    report_qa = read(root / 'review/Final_Report_QA.json')
    assert report_qa['status'] == 'passed'
    assert hashlib.sha256((root / 'Refinement guided mission results.txt').read_bytes()).hexdigest() == report_qa['report_sha256']
    assert hashlib.sha256((root / 'example/final_results.json').read_bytes()).hexdigest() == report_qa['final_results_sha256']
    print('PASS: frozen final report and QA source linkage', flush=True)
    equal(json.loads(run(['theory/check_refinement_laws.py'], root)),
          read(ROOT / 'theory/refinement_law_checks.json'), 'author exact law checks')
    equal(json.loads(run(['review/independent_exact_checks.py'], root)),
          read(ROOT / 'review/Independent_Exact_Checks.json'), 'independent exact law checks')
    run(['-m', 'unittest', 'test_rehearsal_cache', 'test_delayed_integration', '-v'], root / 'example')
    print('PASS: cache and hand-fixture integration regression tests', flush=True)
    run(['example/compose_final_results.py'], root)
    equal(read(root / 'example/final_results.json'), read(ROOT / 'example/final_results.json'),
          'source-preserving final result recomposition')
    run(['example/summarize_results.py'], root)
    equal(read(root / 'example/cost_summary.json'), read(ROOT / 'example/cost_summary.json'),
          'fixed-result cost summary (including retained runtime observations)')
    run(['example/analyze_matched.py'], root)
    equal(read(root / 'example/matched_analysis.json'), read(ROOT / 'example/matched_analysis.json'),
          'fixed-result matched comparisons')
    summary_check = json.loads(run(['review/independent_summary_checks.py'], root))
    assert summary_check['status'] == 'passed'
    print('PASS: independent aggregate/matched/prefix/by-regime summary checks', flush=True)
    run(['review/independent_execution_checks.py', '--results', 'example/final_results.json',
         '--output', 'review/Independent_Execution_Replay.json'], root)
    equal(read(root / 'review/Independent_Execution_Replay.json'),
          read(ROOT / 'review/Independent_Execution_Replay.json'),
          'independent full retained-trace and certificate replay')
    run(['review/independent_execution_checks.py', '--results', 'example/v1/mission_results.json',
         '--output', 'review/Independent_Execution_Replay_v1.json'], root)
    equal(read(root / 'review/Independent_Execution_Replay_v1.json'),
          read(ROOT / 'review/Independent_Execution_Replay_v1.json'),
          'independent original-v1 retained-trace and certificate replay')
print('PASS: all reproduction checks')
