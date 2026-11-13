"""Supplemental semantic-guard repair. Reuses frozen data; no acquisition."""
import json,itertools,hashlib
from copy import deepcopy
from pathlib import Path
import numpy as np
from experiment import Interface,validate_interface,check,coherent,DependencyCache

def main():
    root=Path(__file__).parent;out=root/'results';base=Interface(**json.loads((out/'n5_seed731_global_interface.json').read_text()))
    bad=deepcopy(base);bad.A[0]=[0,.5,0,0,0];bad.B[0]=[0,0,.25,0,0]
    d=np.array([1,.5,.5,.5,.5]);u=(d<=.75).astype(float)
    load=d+np.array(bad.A)@u+np.array(bad.B)@u
    assert load[0]==1.75 and sum(bad.A[0])+sum(bad.B[0])==.75
    assert not validate_interface(bad)
    assert not check(bad,[-1]*5,10,DependencyCache(5))[0]
    assert not coherent(bad,[-1]*5,10,DependencyCache(5).factors)
    # Exhaust all local activation patterns and independent held backgrounds at
    # relevant piecewise vertices {.0,.75,1}; each active choice requires d<=.75.
    A=np.array(base.A);B=np.array(base.B);verified=0
    for background in itertools.product((0.,.75,1.),repeat=5):
        d=np.array(background);eligible=d<=.75
        for bits in itertools.product((0.,1.),repeat=5):
            u=np.array(bits)
            if np.any((u==1)&~eligible):continue
            zero=np.zeros(5)
            for now,past in [(u,zero),(u,u),(zero,u),(zero,zero)]:
                assert np.max(d+A@now+B@past)<=1.5
                verified+=1
    data=json.loads((out/'results.json').read_text());rechecked=0
    for case in data['family_runs']:
        i=Interface(**json.loads((out/f"{case['id']}_interface.json").read_text()));assert validate_interface(i)
        cache=DependencyCache(case['n'])
        updates={'source_retracted':[('sources',False)],'multiple_retractions':[('physical0',False),('protocol',False)],
          'partial_restore':[('sources',True),('physical0',True)],'restore':[('protocol',True)],
          'graph_retracted':[('graph',False)],'graph_restored':[('graph',True)]}
        splitcase=next(x for x in json.loads((out/'split_trace_regression.json').read_text())['cases'] if x['case']==case['id'])
        for record in case['outcomes']:
            name=record['variant']
            for key,value in updates.get(name,[]):cache.change(key,value)
            ends=splitcase['endpoints'] if name=='split_windows' else [-1]*case['n']
            lease=2 if name=='expiry_before_tail' else 10
            assert check(i,ends,lease,cache)[0]==record['accepted']
            assert coherent(i,ends,lease,cache.factors)==record['accepted'];rechecked+=1
    result={'counterexample_old_row_sum':.75,'counterexample_inactive_load':float(load[0]),
      'repaired_checkers_both_reject':True,'canonical_vertex_trace_checks':verified,
      'unchanged_frozen_decisions_rechecked':rechecked,
      'premises':'Independent held d_i in[0,1]; all-good own-report gate d_i<=.75; initial idle command history; hard dynamics remain valid.',
      'guard':'total row<=.75 AND external-current+all-lag row<=.5',
      'proof':'Active: d_i<=.75 plus total<=.75. Inactive: d_i<=1 plus external+lag<=.5. Stop tail is included. Nonnegative coefficients.'}
    (out/'physical_guard_regression.json').write_text(json.dumps(result,indent=2))
    files=['experiment.py','versions/experiment_before_inactive_guard.py','physical_guard_regression.py','results/physical_guard_regression.json','results/results.json']
    (root/'SEMANTIC_GUARD_REPAIR_MANIFEST.json').write_text(json.dumps({f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files},indent=2));print(result)
if __name__=='__main__':main()
