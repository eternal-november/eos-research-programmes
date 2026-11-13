#!/usr/bin/env python3
"""Non-author source-level mutation replay, preserving the real author source.

This is additional C3 negative-control evidence. Every mutant runs the complete
author main from an isolated source tree with exact contract/target copies.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    args = p.parse_args()
    root = args.root.resolve()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    src = root / 'research/workstream_C3/finite/check_c3.py'
    original = src.read_text()
    before = digest(src)
    mutations = {
        'erase_cross_edges_in_reconstruct': ('edges = set(cross)', 'edges = set()'),
        'misclassify_internal_pairs_as_cross': ('if membership[x] != membership[y])', 'if membership[x] == membership[y])'),
    }
    rows = []
    for name, (old, new) in mutations.items():
        assert original.count(old) == 1, (name, original.count(old))
        base = out / name
        script = base / 'research/workstream_C3/finite/check_c3.py'
        script.parent.mkdir(parents=True, exist_ok=True)
        script.write_text(original.replace(old, new))
        for rel in ('research/CompletionContract.md', 'research/workstream_C3/C3_Targets.md'):
            dest = base / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes((root / rel).read_bytes())
        proc = subprocess.run([sys.executable, str(script), '--output', str(base / 'unexpected_certificate.json')],
                              cwd=base, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (base / 'run.log').write_text(proc.stdout)
        assert proc.returncode != 0 and 'AssertionError' in proc.stdout
        assert not (base / 'unexpected_certificate.json').exists()
        if name == 'erase_cross_edges_in_reconstruct':
            assert 'assert reconstruct(h, blocks, cross) == g' in proc.stdout
        else:
            assert 'assert len(x) == exponent' in proc.stdout
        rows.append({'mutation': name, 'source_sha256': digest(script), 'returncode': proc.returncode,
                     'detected_by_real_model_assertion': True, 'log': str((base / 'run.log').relative_to(out))})
    assert digest(src) == before
    report = {'status':'PASS', 'author_source_sha256':before, 'mutations':rows,
              'source_unchanged':True, 'no_author_model_imports':True,
              'scope':'Two independent source mutations supplement the eight executed wrong-map author controls.'}
    (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
