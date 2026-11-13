#!/usr/bin/env python3
"""Fresh C1 verification; leaves all checkpoint sources and evidence unchanged.
Requires pinned Lean 4.35.0 and the lockfile's public dependencies installed.
This verifies implementation/evidence, not independent mathematical acceptance.
"""
from pathlib import Path
import datetime, importlib.util, json, os, re, subprocess, sys, traceback
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('inherited_B_verifier', ROOT/'scripts/verify_workstream_B.py')
b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
base = b.base
CONTRACT = '47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET = '7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e'
C = ROOT/'research/workstream_C1'

def verify_baseline():
    record = json.loads((C/'evidence/Baseline_Archive.json').read_text())
    for item in record['files']:
        if base.digest(ROOT/item['path']) != item['sha256']:
            raise RuntimeError('Delivered A/B baseline changed: '+item['path'])
    assert base.digest(ROOT/'research/CompletionContract.md') == CONTRACT
    assert base.digest(C/'C1_Targets.md') == TARGET
    print('Canonical delivered A/B baseline unchanged:', len(record['files']), 'files', flush=True)

def verify_snapshot():
    snapshot = C/'C1_SourceSnapshot.sha256'
    if not snapshot.exists(): raise RuntimeError('Missing final C1 source snapshot')
    for line in snapshot.read_text().splitlines():
        expected, rel = line.split('  ', 1)
        if base.digest(ROOT/rel) != expected: raise RuntimeError('C1 snapshot mismatch: '+rel)
    for source in sorted((C/'lean').glob('*.lean')):
        if re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom|implemented_by)\b', base.lean_code(source.read_text())):
            raise RuntimeError('Forbidden proof placeholder/custom axiom/oracle: '+str(source))
    print('C1 snapshot and Lean source screen passed', flush=True)

def stable(x):
    volatile = {'started_utc','finished_utc','duration_seconds','python','python_version'}
    if isinstance(x, dict): return {k: stable(v) for k,v in x.items() if k not in volatile}
    if isinstance(x, list): return [stable(v) for v in x]
    return x

def compare_json(actual, expected):
    if stable(json.loads(actual.read_text())) != stable(json.loads(expected.read_text())):
        raise RuntimeError('Reproduced finite certificate differs: '+str(actual))

def main():
    out = ROOT/'reproduction_C1'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out.mkdir(parents=True)
    summary = {'status':'RUNNING','contract_sha256':CONTRACT,'target_sha256':TARGET,
      'reproduction_dir':str(out.relative_to(ROOT)),
      'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        verify_baseline(); verify_snapshot()
        base.run(['bash','verify_workstream_B.sh'], out/'inherited-AB-full.log')
        version = subprocess.check_output(['lean','--version'],cwd=ROOT,text=True)
        if not re.search(r'\bversion 4\.35\.0\b', version): raise RuntimeError(version)
        build = out/'fresh-lean'; (build/'WitnessedDecompositions').mkdir(parents=True)
        env = json.loads(subprocess.check_output(['lake','env',sys.executable,'-c',
          'import json,os;print(json.dumps(dict(os.environ)))'],cwd=ROOT,text=True))
        env['LEAN_PATH'] = str(build)+os.pathsep+env.get('LEAN_PATH','')
        for name in b.BASE_MODULES+b.B_MODULES:
            base.run(['lean','-R','.', '-o',build/'WitnessedDecompositions'/f'{name}.olean',
              f'WitnessedDecompositions/{name}.lean'],out/f'{name}.log',env)
        rewrite = ROOT/'research/workstream_A/rewrite'
        base.run(['lean','-R',rewrite,'-o',build/'GraphCoordinates.olean',rewrite/'GraphCoordinates.lean'],
          out/'GraphCoordinates.log',env)
        lean = C/'lean'
        base.run(['lean','-R',lean,'-o',build/'GraphCutFragment.olean',lean/'GraphCutFragment.lean'],
          out/'GraphCutFragment.log',env)
        audit = 'research/workstream_C1/lean/GraphCutAxioms.lean'
        log = base.run(['lean','-R',lean,ROOT/audit],out/'GraphCutAxioms.log',env)
        base.audit_axioms(audit,log,base.STANDARD)
        probes = C/'review/lean_independent'
        positive = 'research/workstream_C1/review/lean_independent/IndependentChecks.lean'
        log = base.run(['lean',ROOT/positive],out/'IndependentChecks.log',env)
        base.audit_axioms(positive,log,base.STANDARD)
        negatives = []
        for source in sorted(probes.glob('negative_*.lean')):
            proc = subprocess.run(['lean',str(source)],cwd=ROOT,env=env,text=True,
                stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            (out/(source.stem+'.log')).write_text(proc.stdout)
            if source.stem in {'negative_overlap','negative_reverse_arrow'}:
                correct_error = 'Tactic `decide` proved' in proc.stdout and 'is false' in proc.stdout
            else:
                correct_error = 'type mismatch' in proc.stdout.lower()
            if proc.returncode != 1 or not correct_error:
                raise RuntimeError('Negative probe failed for unintended reason: '+source.name)
            negatives.append({'source':str(source.relative_to(ROOT)),
                'sha256':base.digest(source),'expected_rejection':True,'exit_code':proc.returncode})
        if len(negatives) != 6: raise RuntimeError('Expected all six independent Lean negative probes')
        (out/'negative-probes.json').write_text(json.dumps(negatives,indent=2)+'\n')
        base.run([sys.executable,C/'finite/check_c1.py','--output',out/'author-finite.json'],
          out/'author-finite.log')
        compare_json(out/'author-finite.json',C/'finite/results.json')
        independent = C/'review/finite_independent/independent_check.py'
        # Redirect only the checker's output directory after loading its exact
        # unchanged source. ROOT remains the actual repository. No check is altered.
        wrapper = '''import importlib.util,sys
from pathlib import Path
spec=importlib.util.spec_from_file_location('independent_c1_reproduction',sys.argv[1])
m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m)
m.HERE=Path(sys.argv[2]);sys.argv=[sys.argv[1],'--full-product'];m.main()
'''
        base.run([sys.executable,'-c',wrapper,independent,out],out/'independent-finite.log')
        compare_json(out/'independent_results.json',C/'review/finite_independent/independent_results.json')
        verify_baseline(); verify_snapshot()
        summary.update(status='PASS',lean_version=version.strip(),
          explicit_fresh_source_modules=b.BASE_MODULES+b.B_MODULES+['GraphCoordinates','GraphCutFragment'],
          source_snapshot_sha256=base.digest(C/'C1_SourceSnapshot.sha256'),
          claim='C1 implementation/evidence reproduction only; full C1 remains OPEN pending C5/F2 use.')
    except BaseException as exc:
        summary.update(status='FAIL',error=repr(exc));traceback.print_exc()
    finally:
        summary['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        (out/'result.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
    return 0 if summary['status']=='PASS' else 1

if __name__=='__main__': sys.exit(main())
