#!/usr/bin/env python3
"""Exact small selective-acquisition checks, not a physical experiment."""
from itertools import product
from pathlib import Path
import json

W=tuple(product((0,1), repeat=2))

def run(theta, budget):
    K=set(W); spent=0; records=[]
    # Start stopped; abstention at every diagnostic endpoint is a safe no-op.
    def reject(reason):
        return {'accepted':False,'success':False,'safe':True,'spent':spent,'reason':reason,'records':records}
    if spent+2>budget: return reject('no safe acquisition budget')
    spent+=2; y=sum(theta); records.append(('sum',y))
    K={w for w in K if sum(w)==y}
    assert theta in K
    if y==0: return reject('no completing route in retained class')
    if y==1:
        if spent+1>budget: return reject('no diagnostic budget')
        spent+=1; z=theta[0]; records.append(('coordinate',z))
        K={w for w in K if w[0]==z}
        assert theta in K
    choices=[i for i in range(2) if all(w[i]==1 for w in K)]
    if not choices: return reject('no certified continuation')
    if spent+3>budget: return reject('remaining total budget insufficient')
    selected=min(choices)
    assert theta[selected]==1
    spent+=3
    assert spent<=budget
    return {'accepted':True,'success':True,'safe':True,'spent':spent,'selected':selected,'records':records}

cases=[]
for B in range(8):
    for theta in W:
        result=run(theta,B)
        assert result['safe'] and result['spent']<=B
        assert result['accepted']==result['success']
        cases.append({'theta':theta,'budget':B,**result})
assert not run((0,0),100)['success'] # initial class not universally viable
assert all(run(t,6)['success'] for t in W if t!=(0,0))
# Forgetting prior acquisition expense would accept a 3-cost continuation
# under budget 5 despite actual acquisition 3 + continuation 3 = 6.
assert not run((0,1),5)['accepted'] and 3<=5<3+3
out={'status':'PASS','exact_cases':len(cases),
     'true_mechanism_retained':True,'acquisition_and_continuation_budgeted':True,
     'safe_abstention_is_not_completion':True,
     'initial_all_zero_obstruction':True,
     'accepted_iff_program_success_under_exact_contract':True,
     'ignoring_acquisition_cost_counterexample':True,
     'limitation':'Small deterministic contract test only; no acceptance-frequency or hardware guarantee.',
     'cases':cases}
Path(__file__).with_name('selective_completion_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))
