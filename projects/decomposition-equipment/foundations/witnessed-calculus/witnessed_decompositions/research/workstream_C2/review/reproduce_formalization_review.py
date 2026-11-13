#!/usr/bin/env python3
"""Fresh, nonauthor C2 source replay. Requires pinned `lake`/`lean` on PATH.
Rebuilds project dependency sources; reuses pinned third-party dependency caches.
Writes no author/baseline source. Default includes independent finite rerun.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
P=argparse.ArgumentParser()
P.add_argument('--output',type=Path,required=True)
P.add_argument('--skip-finite',action='store_true')
A=P.parse_args(); OUT=A.output.resolve(); OUT.mkdir(parents=True,exist_ok=True)
SOURCE=ROOT/'research/workstream_C2/lean/RelationInterface.lean'
EXPECTED='6d8d638c8d2001b02b2e136ba7b609d867436ce6f08a79ffbfb8c4637dcfad6f'
sha=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(SOURCE)==EXPECTED, 'frozen source changed; review must be renewed'
rows=[]
def run(name,command,cwd,negative=False):
    proc=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/(name+'.log')).write_text(proc.stdout)
    if negative:
        assert proc.returncode!=0 and 'type mismatch' in proc.stdout.lower(), (name,proc.returncode,proc.stdout)
        assert 'object file' not in proc.stdout and 'unknown module' not in proc.stdout.lower(), (name,'infrastructure failure')
    else:
        assert proc.returncode==0, (name,proc.returncode,proc.stdout)
    rows.append({'name':name,'command':command,'exit_code':proc.returncode,'expected_rejection':negative})
    return proc.stdout

with tempfile.TemporaryDirectory(prefix='c2_nonauthor_replay_') as temp:
    temp=Path(temp)
    for name in ['lakefile.toml','lake-manifest.json','lean-toolchain','WitnessedDecompositions.lean']:
        shutil.copyfile(ROOT/name,temp/name)
    shutil.copytree(ROOT/'WitnessedDecompositions',temp/'WitnessedDecompositions')
    (temp/'.lake').mkdir()
    (temp/'.lake/packages').symlink_to((ROOT/'.lake/packages').resolve(),target_is_directory=True)
    rel=Path('research/workstream_C2/lean/RelationInterface.lean')
    (temp/rel).parent.mkdir(parents=True)
    shutil.copyfile(SOURCE,temp/rel)
    run('version',['lean','--version'],temp)
    run('fresh_A2_dependency_build',['lake','build','WitnessedDecompositions.FreeExtension'],temp)
    output=Path('.lake/build/lib/lean/research/workstream_C2/lean/RelationInterface.olean')
    (temp/output).parent.mkdir(parents=True,exist_ok=True)
    run('frozen_C2_build',['lake','env','lean','-o',str(output),str(rel)],temp)
    axioms=run('axioms',['lake','env','lean',str(HERE/'lean_audit_evidence/IndependentAxiomAudit.lean')],temp)
    names=re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)",axioms,re.M)
    assert len(names)==44 and len(set(names))==44, ('axiom coverage',names)
    closures=set()
    for x in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',axioms,re.S):
        closures.update(t.strip() for t in x.split(',') if t.strip())
    assert closures <= {'propext','Quot.sound'}, closures
    semantic=run('semantic_checks',['lake','env','lean',str(HERE/'lean_audit_evidence/IndependentSemanticChecks.lean')],temp)
    assert 'sorryAx' not in semantic
    for f in sorted((HERE/'lean_audit_evidence/negative').glob('*.lean')):
        run('negative_'+f.stem,['lake','env','lean',str(f)],temp,True)
    assert sha(temp/rel)==sha(SOURCE)==EXPECTED
run('boundary_guards',[sys.executable,str(HERE/'BoundaryGuards.py')],ROOT)
if not A.skip_finite:
    run('independent_finite',[sys.executable,str(HERE/'IndependentFinite.py'),'--output',str(OUT/'IndependentFinite.json')],ROOT)
    assert sha(OUT/'IndependentFinite.json')==sha(HERE/'IndependentFinite.json')
    run('source_mutations',[sys.executable,str(ROOT/'research/workstream_C2/finite/run_mutations.py'),'--output',str(OUT/'MutationCertificate.json')],ROOT)
    assert sha(OUT/'MutationCertificate.json')==sha(ROOT/'research/workstream_C2/finite/MutationCertificate.json')
report={'status':'PASS','source_sha256':EXPECTED,'fresh_project_dependency_build':True,
        'third_party_caches_reused':True,'declarations_audited':len(names),
        'axiom_union':sorted(closures),'negative_lean_probes':4,'finite_replayed':not A.skip_finite,
        'commands':rows,'scope':'C2 local L/C review only; P separately reviewed; full C2/D2/E OPEN'}
(OUT/'result.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2,sort_keys=True))
