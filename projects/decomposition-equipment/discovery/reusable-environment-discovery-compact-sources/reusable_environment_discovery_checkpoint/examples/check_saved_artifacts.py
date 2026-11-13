#!/usr/bin/env python3
"""Independent saved-record check. Does not call the synthetic generator or audit.
Usage: python check_saved_artifacts.py runs/n12 [runs/n24 ...]
Recomputes every statistical certificate, transducer, and empirical kernel from records.
"""
import hashlib,json,sys
from pathlib import Path
import numpy as np
import check_growing_memory_environment as c

def check(path):
    path=Path(path);manifest=json.loads((path/'public_manifest.json').read_text())
    frozen=json.loads((path/'frozen_mean.json').read_text()); candidate=json.loads((path/'executable_candidate.json').read_text())
    result=json.loads((path/'results.json').read_text());records=np.load(path/'records.npz')
    assert frozen['training_records_sha256']==c.sha(path/'records.npz')
    assert result['frozen_mean_sha256']==c.sha(path/'frozen_mean.json')
    assert frozen['models']==candidate['mean']
    models=candidate['mean'];actions=records['actions'];y=records['readouts'];n=y.shape[1]
    for m in models:
        assert isinstance(m['intercept'],int)
        assert all(isinstance(w,int) and 0<=col<n*(c.L+1) for col,w in m['linear'])
        assert all(isinstance(w,int) and 0<=a<n and n<=b<n*(c.L+1) for a,b,w in m['interactions'])
    train=manifest['train_rows'];validate=manifest['validation_rows']
    pred,support=c.support_validate(actions,y,models,train,validate)
    assert support==result['support_certificate'] and support['passed']
    z=y[train+validate:].astype(int)-pred[train+validate:].astype(int);split=len(z)//2
    groups,gcert,_=c.recover_groups(z[:split]);gcert['calibration_rows']=split
    assert groups==result['discovered_noise_groups']
    assert gcert==result['joint_group_certificate']
    assert manifest['promised_minimum_finest_block_split_TV_gap']>gcert['required_true_block_split_gap_for_completeness']
    kernels,pcert=c.estimate_kernels(z[split:],groups)
    assert json.loads(json.dumps(kernels))==candidate['joint_innovation_interfaces']
    assert pcert==result['probability_certificate']
    memory=[c.quotient_for_channel(models,n,j) for j in range(n)]
    assert json.loads(json.dumps(memory))==candidate['memory_transducers']
    # Re-execute compressed memory under genuinely output-dependent controllers.
    c.feedback_checks(models,kernels,memory,n,20261029+n)
    return {'path':str(path),'records_only_certificates_recomputed':True,'n':n,
            'conditional_failure_bound':result['conditional_failure_probability_upper_bound'],
            'generator_or_synthetic_audit_called':False}

if __name__=='__main__':
    results=[check(p) for p in sys.argv[1:]]
    print(json.dumps(results,indent=2))
