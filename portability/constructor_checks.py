"""Exact algorithm checks and rejection witnesses, not a whole-source verifier."""
from __future__ import annotations
import json
from dataclasses import replace
from fractions import Fraction as Q
from itertools import combinations, product
from constructors import (CertificateFailure, PhaseEdge, WindowEnvelope, check_horizon,
                          matrix_rank, phase_budget, projected_support, reservoir_margin,
                          separating_bundle)


def need(ok, reason):
    if not ok:
        raise AssertionError(reason)


def rejects(call, substring):
    try:
        call()
    except CertificateFailure as error:
        need(substring in str(error), f'Wrong failure: {error}')
        return str(error)
    raise AssertionError('Invalid certificate was accepted')


def run():
    footprints={f'e{i}': {'raw': frozenset({i}), 'execution': frozenset({0})} for i in range(6)}
    old=projected_support(footprints, footprints, 'raw')
    footprints['e0']['raw']=frozenset({0,6})
    changed=projected_support(footprints, footprints, 'raw')
    need(len(old)==6 and len(changed)==7, 'Incident identity collapsed to execution host')
    need(len(projected_support(footprints, footprints, 'execution'))==1, 'Separate projections lost')
    missing=rejects(lambda:projected_support(['missing'],footprints,'raw'),'Unspecified incident')

    rows=[(Q(1),Q(i)) for i in range(6)]
    supports=[frozenset({i}) for i in range(6)]
    bundle=separating_bundle(rows,supports,2,6,1000)
    need(len(bundle.rows)==4, 'Wrong separating-bundle size')
    altered=[frozenset({0,1}),*supports[2:]]
    new_bundle=separating_bundle(rows,altered,2,6,1000)
    need(len(new_bundle.rows)==4 and new_bundle.rows != bundle.rows, 'New bundle did not replace failed old incidence')
    need(any(matrix_rank([rows[i] for i in bundle.rows if i not in a|b],2)<2
             for a,b in product(altered, repeat=2)), 'Old adapter still passed changed incidence')
    # Independent 2-column rank characterization by determinants on all small integer row sets.
    rank_cases=0
    row_domain=list(product(range(-1,2),repeat=2))
    for selected in combinations(row_domain,3):
        expected=2 if any(a[0]*b[1]-a[1]*b[0] for a,b in combinations(selected,2)) else int(any(any(r) for r in selected))
        need(matrix_rank(selected,2)==expected,'Gaussian rank disagrees with determinant characterization')
        rank_cases+=1
    search_limit=rejects(lambda:separating_bundle(rows,supports,2,6,1),'capacity exhausted')
    rank_failure=rejects(lambda:separating_bundle([(1,0)]*6,supports,2,6,1000),'No separating bundle')

    ranks={'entry':3,'write':2,'abort':1,'done':0}
    edges=[PhaseEdge('entry','write',Q(2),Q(4),'entry operations'),
           PhaseEdge('entry','abort',Q(7),Q(1),'failed entry branch'),
           PhaseEdge('write','done',Q(3),Q(9),'write and close'),
           PhaseEdge('abort','done',Q(2),Q(2),'bounded abort')]
    cert=phase_budget(ranks,frozenset({'done'}),edges,'entry')
    # Independently enumerate every path for the finite fixture.
    stack=[('entry',Q(0),Q(0))];paths=[]
    while stack:
        state,time,work=stack.pop()
        if state=='done':paths.append((time,work))
        else:stack.extend((e.target,time+e.elapsed,work+e.work) for e in edges if e.source==state)
    need(cert.time_bound==max(t for t,w in paths)==9 and cert.work_bound==max(w for t,w in paths)==13,
         'Demonic bound omitted a branch or mixed incompatible maxima')
    cycle=rejects(lambda:phase_budget(ranks,frozenset({'done'}),[*edges,PhaseEdge('abort','entry',Q(1),Q(1),'retry')],'entry'),'Nondecreasing')
    stall=rejects(lambda:phase_budget(ranks,frozenset({'done'}),edges[:-1],'entry'),'stalled nonterminal')
    negative=rejects(lambda:phase_budget({'a':1,'z':0},frozenset({'z'}),[PhaseEdge('a','z',Q(-1),Q(1),'bad')],'a'),'Negative phase cost')
    envelope=WindowEnvelope(1,2,Q(3),Q(1,100))
    joint=check_horizon(envelope,Q(12),Q(1),cert,Q(1),6)
    need(joint.support_budget==6 and joint.slack==1,'Joint horizon witness changed')
    late=rejects(lambda:check_horizon(envelope,Q(11),Q(1),cert,Q(1),6),'strict completion')
    wide=rejects(lambda:check_horizon(envelope,Q(100),Q(1),cert,Q(1),6),'support exceeds')
    fractional=rejects(lambda:WindowEnvelope(Q(1,2),0,Q(0),Q(0)).bound(Q(1),Q(1)), 'integer')
    floating=rejects(lambda:check_horizon(envelope,Q(12),0.1,cert,Q(1),6),'exact int or Fraction')
    forged=rejects(lambda:check_horizon(envelope,Q(12),Q(1),replace(cert,time_bound=Q(-1)),Q(1),6),'differs from its ranked graph')
    boolean=rejects(lambda:separating_bundle(rows,supports,True,6,1000),'positive integer')
    margin=reservoir_margin(Q(20),Q(2),Q(3),Q(4),Q(2))
    need(margin==12,'Reservoir arithmetic changed')
    deficit=rejects(lambda:reservoir_margin(Q(20),Q(2),Q(3),Q(2),Q(2)),'Long-run supply')
    return dict(scope='finite algorithm checks and rejection witnesses; no source mission or RP completion claim',
                incidence=dict(before=sorted(old),after=sorted(changed),execution_hosts=1),
                bundles=dict(original=bundle.rows,changed=new_bundle.rows,determinant_crosschecks=rank_cases),
                phase=dict(time=str(cert.time_bound),work=str(cert.work_bound),all_paths=[list(map(str,p)) for p in paths]),
                horizon=dict(H=str(joint.horizon),support=joint.support_budget,slack=str(joint.slack)),
                reserve_margin=str(margin),rejections=[missing,search_limit,rank_failure,cycle,stall,negative,late,wide,deficit,fractional,floating,forged,boolean],
                program_completion=False)


if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
