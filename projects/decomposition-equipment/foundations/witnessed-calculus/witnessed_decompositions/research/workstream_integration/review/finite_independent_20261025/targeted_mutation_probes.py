#!/usr/bin/env python3
"""Supplement early-exit author mutation tests; never claims relation independence."""
from pathlib import Path
import sys,subprocess,json,hashlib
P=Path(__file__).parent
base=Path(sys.argv[1]).resolve()
probes={
'omit_MIn':r'''
from model import *
import check_integration as C
counts={'contextual_validator_rejections':0,'bare_validator_rejections':0,'raw_added_tower_instances':0}
for M in MONOIDS:
    leaf=L(Graph(1),Arrow(0,1));left=D(0,leaf)
    for name,host,address in C.contexts(L(leaf.graph,leaf.arrow),M):
        index=C.leaf_addresses(host).index(address);ls=tuple(leaves(host))
        F=ls[:index]+(left,)+ls[index+1:];H=ls[:index]+(leaf,)+ls[index+1:]
        target=graft(host,H)
        assert apply_step(graft(host,F),address,'D0',M)==target
        try:C.check_paths(host,(Raw(F),Eq(target,address,'D0')),(Raw(H),),M,'MIn_targeted')
        except AssertionError as e:assert str(e)=='MIn certificate not admitted by syntactic basis'
        else:raise AssertionError('mutant contextual MIn unexpectedly admitted')
        counts['bare_validator_rejections' if name=='id' else 'contextual_validator_rejections']+=1
    for leaf in tuple(leaves(C.six_term(M)))+(L(Graph(0),Arrow(1,1)),):
        seen=[]
        for h in range(9):
            tower=leaf
            for _ in range(h):tower=D(0,tower)
            F,target=path_normalize(leaf,(Raw((tower,)),)+C.eq_trace(tower,M),M)
            assert target==leaf and F==(tower,) and node_count(F[0])==h
            assert address_evaluation(F[0],M)==address_evaluation(leaf,M)
            seen.append(node_count(F[0]));counts['raw_added_tower_instances']+=1
        assert seen==list(range(9))
print(__import__('json').dumps(counts))
''',
'erase_nullary_value':r'''
from model import *
import check_integration as C
counts={'typed_MIn_nullary_paths_checked':0,'independent_local_value_disagreements':0}
for M in MONOIDS:
    for v in range(1,M.size):
        for a in range(3):
            host=L(Graph(0),Arrow(a,a));unit=D(v,U(a));left=D(0,unit)
            C.check_paths(host,(Raw((left,)),Eq(unit,(),'D0')),(Raw((unit,)),),M,'MIn_targeted_unit')
            assert address_evaluation(unit,M).value==v
            assert evaluation(unit,M).value==0
            assert evaluation(unit,M)!=address_evaluation(unit,M)
            counts['typed_MIn_nullary_paths_checked']+=1;counts['independent_local_value_disagreements']+=1
print(__import__('json').dumps(counts))
'''}
rows=[]
for name,source in probes.items():
    folder=base/'mutations'/name
    assert folder.is_dir()
    r=subprocess.run([sys.executable,'-c',source],cwd=folder,text=True,capture_output=True)
    log=P/(name+'_targeted.log');log.write_text(r.stdout+r.stderr)
    assert r.returncode==0,(name,r.stderr)
    rows.append({'mutant':name,'status':'EXPECTED_DEFECT_DETECTED','counts':json.loads(r.stdout),'mutant_sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (folder/'model.py',folder/'check_integration.py')},'probe_text_sha256':hashlib.sha256(source.encode()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
report={'status':'PASS','limitation':'MIn omission is syntactic validator rejection plus bounded invariant illustrations; nullary path is syntactically valid but independently compared recursive local evaluation is corrupt. Neither is a necessity proof.','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'probes':rows}
(P/'TargetedMutationCertificate.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
