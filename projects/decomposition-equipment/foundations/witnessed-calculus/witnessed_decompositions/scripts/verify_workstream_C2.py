#!/usr/bin/env python3
"""Reproduce the C2 local checkpoint without reusing project proof objects.
Public dependencies must be installed at unchanged lake-manifest revisions.
C evidence stays C. A successful run is not mathematical acceptance.
"""
from pathlib import Path
import datetime, hashlib, importlib.util, json, os, re, subprocess, sys, traceback
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('inherited_C1_verifier',ROOT/'scripts/verify_workstream_C1.py')
c1=importlib.util.module_from_spec(spec);spec.loader.exec_module(c1)
b=c1.b;base=c1.base
C=ROOT/'research/workstream_C2'
CONTRACT='47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET='b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4'

def invariants():
    rec=json.loads((C/'BaselinePreservation.json').read_text())
    assert rec['baseline_file_count']==445
    for x in rec['files']:
        assert base.digest(ROOT/x['path'])==x['sha256'], 'Baseline changed: '+x['path']
    assert base.digest(ROOT/'research/CompletionContract.md')==CONTRACT
    assert base.digest(C/'C2_Targets.md')==TARGET
    snap=C/'C2_SourceSnapshot.sha256'
    for line in snap.read_text().splitlines():
        expected,rel=line.split('  ',1)
        assert base.digest(ROOT/rel)==expected, 'C2 snapshot mismatch: '+rel
    for source in (C/'lean').glob('*.lean'):
        assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom|implemented_by)\b',base.lean_code(source.read_text())),source
    print('445 baseline files, contract, target, C2 source snapshot and Lean screen PASS',flush=True)

def compare(actual,expected):
    c1.compare_json(actual,expected)

def main():
    out=ROOT/'reproduction_C2'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out.mkdir(parents=True)
    report={'status':'RUNNING','contract_sha256':CONTRACT,'target_sha256':TARGET,
            'reproduction_dir':str(out.relative_to(ROOT)),
            'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        invariants()
        base.run(['bash','verify_workstream_C1.sh'],out/'inherited-ABC1-full.log')
        version=subprocess.check_output(['lean','--version'],cwd=ROOT,text=True)
        assert re.search(r'\bversion 4\.35\.0\b',version),version
        build=out/'fresh-lean';(build/'WitnessedDecompositions').mkdir(parents=True)
        env=json.loads(subprocess.check_output(['lake','env',sys.executable,'-c',
          'import json,os;print(json.dumps(dict(os.environ)))'],cwd=ROOT,text=True))
        env['LEAN_PATH']=str(build)+os.pathsep+env.get('LEAN_PATH','')
        for name in b.BASE_MODULES+b.B_MODULES:
            base.run(['lean','-R','.', '-o',build/'WitnessedDecompositions'/f'{name}.olean',
              f'WitnessedDecompositions/{name}.lean'],out/f'{name}.log',env)
        lean=C/'lean'
        (build/'research/workstream_C2/lean').mkdir(parents=True)
        base.run(['lean','-R','.', '-o',build/'research/workstream_C2/lean/RelationInterface.olean',lean/'RelationInterface.lean'],
          out/'RelationInterface.log',env)
        audit='research/workstream_C2/lean/AxiomAudit.lean'
        log=base.run(['lean','-R','.',ROOT/audit],out/'C2AxiomAudit.log',env)
        base.audit_axioms(audit,log,{'propext','Quot.sound'})
        probes=C/'review/lean_audit_evidence'
        for name in ['IndependentSemanticChecks','IndependentAxiomAudit']:
            rel='research/workstream_C2/review/lean_audit_evidence/'+name+'.lean'
            log=base.run(['lean','-R','.',ROOT/rel],out/(name+'.log'),env)
            base.audit_axioms(rel,log,{'propext','Quot.sound'})
        negative=[]
        for name in ['ExactConflation','NonloopNullary','ReverseContainment','VacuousSurjectivityNullary']:
            src=probes/'negative'/(name+'.lean')
            proc=subprocess.run(['lean','-R','.',str(src)],cwd=ROOT,env=env,text=True,
                stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            (out/('negative-'+name+'.log')).write_text(proc.stdout)
            assert proc.returncode==1 and 'type mismatch' in proc.stdout.lower(), (name,proc.returncode,proc.stdout)
            negative.append({'source':str(src.relative_to(ROOT)),'sha256':base.digest(src),'expected_type_rejection':True})
        (out/'independent-negative-probes.json').write_text(json.dumps(negative,indent=2)+'\n')
        base.run([sys.executable,C/'finite/check_c2_model.py','--output',out/'author.json'],out/'author.log')
        compare(out/'author.json',C/'finite/AuthorCertificate.json')
        base.run([sys.executable,C/'finite/run_mutations.py','--output',out/'mutations.json'],out/'mutations.log')
        compare(out/'mutations.json',C/'finite/MutationCertificate.json')
        base.run([sys.executable,C/'review/IndependentFinite.py','--output',out/'independent.json'],out/'independent.log')
        compare(out/'independent.json',C/'review/IndependentFinite.json')
        invariants()
        report.update(status='PASS',lean_version=version.strip(),baseline_unchanged=445,
          source_snapshot_sha256=base.digest(C/'C2_SourceSnapshot.sha256'),
          fresh_project_modules=b.BASE_MODULES+b.B_MODULES+['RelationInterface'],
          finite_certificates=['F1-F6 author','F1-F6 independent','four executed source mutations'],
          claim='C2 local source/evidence reproduction only; full C2 OPEN pending D2/E use.')
    except BaseException as exc:
        report.update(status='FAIL',error=repr(exc));traceback.print_exc()
    finally:
        report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2),flush=True)
    return 0 if report['status']=='PASS' else 1
if __name__=='__main__':sys.exit(main())
