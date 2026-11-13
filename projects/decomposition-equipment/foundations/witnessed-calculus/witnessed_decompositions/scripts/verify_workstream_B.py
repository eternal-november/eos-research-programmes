#!/usr/bin/env python3
"""Reproduce B1/B2 without altering baseline sources or historical evidence.

The pinned external Lean/mathlib installation/cache is a prerequisite, just as
for the original A export. New project sources are explicitly compiled into a
fresh directory, so stale project oleans cannot count as final evidence.
"""
from pathlib import Path
import datetime, hashlib, importlib.util, json, os, re, subprocess, sys, traceback
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('original_export_verifier',ROOT/'scripts/verify_export.py')
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
BASE_MODULES=['Core','Examples','Collections','PathOccurrences','Positive','TreeOccurrences',
              'Calculus','FreeCalculus','FreeExtension','FreeAdjunction','Congruence',
              'QuotientCalculus','PresentedCalculus','WeightInvariant','PresentationExamples']
B_MODULES=['RawRefinement','SemanticRefinement','RefinementFunctoriality','RefinementLifting','RefinementComparison','RefinementExamples']
AUDITS=[('audit/WorkstreamB1Axioms.lean',base.CORE),
        ('audit/WorkstreamB2Axioms.lean',base.CORE),
        ('audit/WorkstreamB2LiftingAxioms.lean',base.STANDARD),
        ('audit/WorkstreamB2FunctorialityAxioms.lean',base.STANDARD),
        ('audit/WorkstreamB2BridgeAxioms.lean',base.STANDARD),
        ('audit/WorkstreamB2ExampleAxioms.lean',base.STANDARD),
        ('tests/B1RawRefinementAudit.lean',base.CORE),
        ('tests/B2RefinementExamples.lean',base.STANDARD),
        ('tests/B2RawEvaluationAudit.lean',base.STANDARD),
        ('research/workstream_B/review/B1_Lean_Independent/AllB1Axioms.lean',base.CORE),
        ('research/workstream_B/review/B1_Lean_Independent/IndependentB1Checks.lean',base.CORE),
        ('research/workstream_B/review/B2_Independent/AllB2CoreExampleAxioms.lean',base.STANDARD),
        ('research/workstream_B/review/B2_Independent/IndependentCompositeChecks.lean',base.STANDARD),
        ('research/workstream_B/review/B2_Independent/IndependentComparisonChecks.lean',base.STANDARD)]
CONTRACT='47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET='37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092'


def verify_baseline():
    record=json.loads((ROOT/'research/workstream_B/evidence/Baseline_Imported.json').read_text())
    for item in record['files']:
        if base.digest(ROOT/item['path']) != item['sha256']:
            raise RuntimeError('Original imported source/checkpoint changed: '+item['path'])
    assert base.digest(ROOT/'research/CompletionContract.md')==CONTRACT
    assert base.digest(ROOT/'research/workstream_B/B1_B2_Targets.md')==TARGET
    print(f"All {len(record['files'])} imported baseline files and approved target freeze unchanged.")


def source_files():
    return [ROOT/'WitnessedDecompositions'/f'{n}.lean' for n in B_MODULES]+[
        ROOT/source for source,_ in AUDITS]+[ROOT/'WorkstreamB.lean']


def verify_sources():
    for p in source_files():
        code=base.lean_code(p.read_text())
        if re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom|implemented_by)\b',code):
            raise RuntimeError('Forbidden placeholder/custom axiom/unchecked oracle: '+str(p))
    snapshot=ROOT/'research/workstream_B/B1_B2_SourceSnapshot.sha256'
    if not snapshot.exists():
        raise RuntimeError('Final source snapshot is missing; author work is not a frozen checkpoint.')
    for line in snapshot.read_text().splitlines():
        expected,rel=line.split('  ',1)
        if base.digest(ROOT/rel)!=expected:raise RuntimeError('B snapshot mismatch: '+rel)
    print('B snapshot and Lean source screening passed.')


def main():
    out=ROOT/'reproduction_B'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out.mkdir(parents=True)
    summary={'status':'RUNNING','contract_sha256':CONTRACT,'target_sha256':TARGET,
             'reproduction_dir':str(out.relative_to(ROOT)),
             'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        verify_baseline();verify_sources()
        # Run the unchanged complete A export driver, not only its finite checks.
        base.run(['bash','verify_export.sh'],out/'original-export-full.log')
        version=subprocess.check_output(['lean','--version'],cwd=ROOT,text=True)
        if not re.search(r'\bversion 4\.35\.0\b',version):raise RuntimeError(version)
        build=out/'fresh-lean';(build/'WitnessedDecompositions').mkdir(parents=True)
        env=json.loads(subprocess.check_output(['lake','env',sys.executable,'-c',
                       'import json,os;print(json.dumps(dict(os.environ)))'],cwd=ROOT,text=True))
        env['LEAN_PATH']=str(build)+os.pathsep+env.get('LEAN_PATH','')
        for n in BASE_MODULES+B_MODULES:
            base.run(['lean','-R','.', '-o',build/'WitnessedDecompositions'/f'{n}.olean',
                      f'WitnessedDecompositions/{n}.lean'],out/f'{n}.log',env)
        base.run(['lean','-R','.', '-o',build/'WorkstreamB.olean','WorkstreamB.lean'],
                 out/'WorkstreamB.log',env)
        for source,allowed in AUDITS:
            log=base.run(['lean',source],out/(Path(source).stem+'.log'),env)
            base.audit_axioms(source,log,allowed)
        finite=[('research/workstream_B/B1_ChronologyChecks.py',
                 'research/workstream_B/evidence/B1_ChronologyChecks.json','B1-chronology'),
                ('research/workstream_B/examples/check_semantic_refinements.py',
                 'research/workstream_B/evidence/semantic-finite-initial.json','B2-semantic'),
                ('research/workstream_B/review/B1_IndependentChronologySpotcheck.py',
                 'research/workstream_B/review/B1_IndependentChronologySpotcheck.json','B1-independent-chronology')]
        for source,expected,stem in finite:
            output=base.run([sys.executable,source],out/f'{stem}.json')
            base.same_json(ROOT/expected,output)
        verify_baseline();verify_sources()
        summary.update(status='PASS',lean_version=version.strip(),
                       explicit_fresh_source_modules=BASE_MODULES+B_MODULES,
                       source_snapshot_sha256=base.digest(ROOT/'research/workstream_B/B1_B2_SourceSnapshot.sha256'),
                       claim='Implementation/evidence reproduction only; independent acceptance is a separate verdict.')
    except BaseException as exc:
        summary.update(status='FAIL',error=repr(exc))
        traceback.print_exc()
    finally:
        summary['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        (out/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps(summary,indent=2))
    return 0 if summary['status']=='PASS' else 1

if __name__=='__main__':sys.exit(main())
