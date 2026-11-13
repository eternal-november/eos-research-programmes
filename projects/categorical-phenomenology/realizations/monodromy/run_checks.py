#!/usr/bin/env python3
"""Run numerical checks in an isolated copy; do not modify packaged sources.

Usage: python run_checks.py [--include-supplements] [--output-dir run_results]
These are floating-point regressions, not formal or interval proofs.
"""
import argparse, hashlib, json, platform, shutil, subprocess, sys, tempfile, time
from pathlib import Path

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--include-supplements',action='store_true')
    ap.add_argument('--output-dir',default='run_results')
    args=ap.parse_args()
    base=Path(__file__).resolve().parent
    dest=Path(args.output_dir).resolve(); dest.mkdir(parents=True,exist_ok=True)
    try:
        import numpy, scipy
    except ImportError as e:
        print('Missing dependency. Install requirements.txt in a Python environment. '+str(e),file=sys.stderr)
        return 2
    scripts=['monodromy_native_checks.py']
    if args.include_supplements:
        scripts += ['supplements/'+x for x in [
          'topological_native_checks.py','topological_temporal_checks.py',
          'topology_audit_checks.py','topology_finite_example.py',
          'topology_euler_example.py','topology_finite_review_checks.py',
          'topology_finite_euler_review_checks.py','topology_temporal_review_checks.py',
          'affine_independent_checks.py']]
    summary={'scope':'Floating-point formula regression, not a topological proof, interval certificate, or novelty assessment.',
             'python':platform.python_version(),'numpy':numpy.__version__,'scipy':scipy.__version__,
             'source_report_sha256':hashlib.sha256((base/'monodromy_native_report.tex').read_bytes()).hexdigest(),
             'checks':[]}
    with tempfile.TemporaryDirectory(prefix='monodromy-checks-') as td:
        tmp=Path(td)
        for rel in scripts:
            target=tmp/rel; target.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(base/rel,target)
        for rel in scripts:
            t=time.perf_counter()
            r=subprocess.run([sys.executable,str(tmp/rel)],cwd=(tmp/rel).parent,capture_output=True,text=True)
            stdout=r.stdout.replace(str(tmp),'<isolated-check-directory>')
            stderr=r.stderr.replace(str(tmp),'<isolated-check-directory>')
            p=dest/rel; p.parent.mkdir(parents=True,exist_ok=True)
            p.with_suffix('.stdout.txt').write_text(stdout)
            if stderr:p.with_suffix('.stderr.txt').write_text(stderr)
            record={'script':rel,'exit_code':r.returncode,'elapsed_seconds':round(time.perf_counter()-t,3)}
            try:
                data=json.loads(stdout)
                p.with_suffix('.result.json').write_text(json.dumps(data,indent=2)+'\n')
                record['result']=data
            except json.JSONDecodeError:
                record['json_output_valid']=False
            record['passed']=r.returncode==0 and 'result' in record
            summary['checks'].append(record)
            print(('PASS ' if record['passed'] else 'FAIL ')+rel,flush=True)
    summary['all_passed']=all(x['passed'] for x in summary['checks'])
    (dest/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    return 0 if summary['all_passed'] else 1
if __name__=='__main__':raise SystemExit(main())
