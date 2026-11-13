#!/usr/bin/env python3
"""Reviewer-owned fresh source/project-output reproduction; no author build wrapper."""
from pathlib import Path
import os, json, hashlib, shutil, subprocess, re, datetime, traceback
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
SRC=HERE/'source'; BUILD=HERE/'fresh'; LOG=HERE/'logs'
assert not SRC.exists() and not BUILD.exists(), 'Fresh-only runner: preserve previous run instead of overwriting it'
SRC.mkdir(); BUILD.mkdir(); LOG.mkdir()
REC=Path('/workspace/shared/witnessed_B_20261024/toolchain_recovery')
PKG=REC/'baseline/.lake/packages'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
result={'status':'RUNNING','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(), 'commands':[], 'snapshots':[], 'axioms':{},'negative_controls':[]}
def baseline():
    items=json.loads((ROOT/'research/workstream_integration/BaselinePreservation.json').read_text())['files']
    for i in items: assert sha(ROOT/i['path'])==i['sha256'], i['path']
    return len(items)
def save(): (HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
try:
    result['baseline_before']=baseline()
    for p in ROOT.rglob('*.lean'):
        if HERE in p.parents or '/runs/' in str(p) or '/.lake/' in str(p): continue
        rel=p.relative_to(ROOT); dest=SRC/rel; dest.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(p,dest)
        result['snapshots'].append({'path':str(rel),'sha256':sha(dest)})
    result['contract_sha256']=sha(ROOT/'research/CompletionContract.md')
    result['target_sha256']=sha(ROOT/'research/workstream_integration/Integrated_Targets.md')
    assert result['contract_sha256']=='47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
    assert result['target_sha256']=='2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b'
    env=dict(os.environ)
    assert shutil.which('lean'), 'source the documented env.sh before running'
    result['lean_version']=subprocess.check_output(['lean','--version'],text=True).strip()
    assert 'version 4.35.0' in result['lean_version']
    lock=json.loads((ROOT/'lake-manifest.json').read_text())
    result['dependency_revisions']=[]
    external=[]
    for dep in lock['packages']:
        path=PKG/dep['name']
        rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
        assert rev==dep['rev'],(dep['name'],rev,dep['rev'])
        result['dependency_revisions'].append({'name':dep['name'],'rev':rev})
        external.append(str(path/'.lake/build/lib/lean'))
    external.append(str(REC/'lean-4.35.0-linux/lib/lean'))
    env['LEAN_PATH']=os.pathsep.join([str(BUILD)]+external)
    result['LEAN_PATH']=env['LEAN_PATH']
    aliases={n:SRC/'research/workstream_A/rewrite'/f'{n}.lean' for n in ['GraphCoordinates','TypedNormalizerAlgebra','RewriteFragmentCandidate']}
    aliases['GraphCutFragment']=SRC/'research/workstream_C1/lean/GraphCutFragment.lean'
    for n in ['QuotientArrowCertificates','GraphForestNormalForms','PublicExampleBridge']:
        aliases[n]=SRC/'research/workstream_integration/lean'/f'{n}.lean'
    visited=set()
    def run(p,scope=None,module=None,negative=False):
        rel=p.relative_to(SRC); key=str(rel).replace('/','_')
        args=['lean','-R',str(scope or SRC)]
        if module:
            out=BUILD/Path(*module.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
            args+=['-o',str(out)]
        args.append(str(p))
        proc=subprocess.run(args,cwd=SRC,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (LOG/(key+'.log')).write_text(proc.stdout)
        rec={'source':str(rel),'sha256':sha(p),'exit':proc.returncode,'log':str((LOG/(key+'.log')).relative_to(HERE)),'command':args}
        result['commands'].append(rec);save();print(str(rel),proc.returncode,flush=True)
        if negative:
            assert proc.returncode!=0 and ('type mismatch' in proc.stdout.lower() or 'unsolved goals' in proc.stdout.lower() or 'failed' in proc.stdout.lower()), proc.stdout
            assert 'unknown module' not in proc.stdout.lower(),proc.stdout
            result['negative_controls'].append(rec);return
        assert proc.returncode==0,proc.stdout
        expected=len(re.findall(r'^\s*#print\s+axioms\s+',p.read_text(),re.M))
        found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",proc.stdout,re.S)
        empty=re.findall(r"'([^']+)' does not depend on any axioms",proc.stdout)
        assert len(found)+len(empty)==expected,(str(rel),expected,len(found),len(empty))
        for name,closure in found:
            axioms=[s.strip() for s in closure.split(',') if s.strip()]
            assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(name,axioms)
            result['axioms'][name]=axioms
        for name in empty:result['axioms'][name]=[]
    def visit(name):
        if name in visited:return
        p=aliases.get(name,SRC/Path(*name.split('.')).with_suffix('.lean'))
        if not p.exists():return
        visited.add(name)
        for dep in re.findall(r'^(?:public )?import ([\w.]+)',p.read_text(),re.M):visit(dep)
        run(p,p.parent if name in aliases else SRC,name)
    for p in sorted((SRC/'WitnessedDecompositions').glob('*.lean')):visit('WitnessedDecompositions.'+p.stem)
    for name in ['WitnessedDecompositions','WorkstreamB','GraphCoordinates','TypedNormalizerAlgebra','RewriteFragmentCandidate','GraphCutFragment','research.workstream_C2.lean.RelationInterface','QuotientArrowCertificates','GraphForestNormalForms','PublicExampleBridge']:visit(name)
    audits=[SRC/'AxiomAudit.lean',SRC/'FullMathlibSmoke.lean']+sorted((SRC/'audit').glob('*.lean'))+sorted((SRC/'tests').glob('*.lean'))
    audits+=sorted((SRC/'research/workstream_A/relational').glob('*.lean'))
    audits += [SRC/'research/workstream_A/rewrite'/f'{n}.lean' for n in ['TypedNormalizerAlgebraTest','RewriteFragmentCandidateTest']]
    audits += sorted((SRC/'research/workstream_B/review').rglob('*.lean'))
    audits += [SRC/'research/workstream_C1/lean/GraphCutAxioms.lean',SRC/'research/workstream_C1/review/lean_independent/IndependentChecks.lean',SRC/'research/workstream_C2/lean/AxiomAudit.lean']
    audits += sorted((SRC/'research/workstream_C2/review/lean_audit_evidence').glob('*.lean'))
    audits += [SRC/'research/workstream_integration/lean/AxiomAudit.lean']
    for p in audits:
        for dep in re.findall(r'^(?:public )?import ([\w.]+)',p.read_text(),re.M):visit(dep)
        run(p)
    for p in sorted((SRC/'research/workstream_C1/review/lean_independent').glob('negative_*.lean'))+sorted((SRC/'research/workstream_C2/review/lean_audit_evidence/negative').glob('*.lean')):run(p,negative=True)
    result['baseline_after']=baseline();result['status']='PASS'
except BaseException as e:
    result.update(status='FAIL',error=repr(e),traceback=traceback.format_exc());print(result['traceback'],flush=True)
finally:
    result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
raise SystemExit(result['status']!='PASS')
