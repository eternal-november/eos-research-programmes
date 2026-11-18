"""Exact probes of composition laws and the actual accounting failure kinds.

This finite relation fragment is not a hybrid-source simulator or a completed
decentralized strategy-refinement theorem.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

if sys.flags.optimize: raise RuntimeError('Unoptimized Python required')
HERE=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise AssertionError(message)

def compose(R,S):
    return {x:frozenset(z for y in ys for z in S[y]) for x,ys in R.items()}

def wp(R,G):
    return frozenset(x for x,ys in R.items() if ys<=G)

def nwp(R,G):
    return frozenset(x for x,ys in R.items() if ys and ys<=G)

def relation_laws():
    subsets=[frozenset(),frozenset({0}),frozenset({1}),frozenset({0,1})]
    total=[dict(enumerate(rows)) for rows in product(subsets[1:],repeat=2)]
    identity={0:frozenset({0}),1:frozenset({1})}
    wp_cases=0;assoc_cases=0
    for R in total:
        require(compose(identity,R)==R==compose(R,identity),'Identity law fails')
        for S in total:
            RS=compose(R,S)
            require(all(RS.values()),'Composition lost totality')
            for G in subsets:
                require(wp(RS,G)==wp(R,wp(S,G)),'Demonic preimage composition fails')
                require(wp(RS,G)==nwp(RS,G),'Total relation has a hidden blocked branch')
                wp_cases+=1
            for T in total:
                require(compose(RS,T)==compose(R,compose(S,T)),'Associativity fails')
                assoc_cases+=1
    R={'start':frozenset({'a','b'})}
    S={'a':frozenset({'safe'}),'b':frozenset()}
    naive=nwp(compose(R,S),frozenset({'safe'}))
    staged=nwp(R,nwp(S,frozenset({'safe'})))
    require(naive=={'start'} and not staged,'Partial-composition obstruction missing')
    # Retain the blocked outcome before hiding the intermediate state.
    fail='blocked'
    completed={y:zs if zs else frozenset({fail}) for y,zs in S.items()}
    real=compose(R,completed)['start']
    require(real=={'safe',fail},'Failure completion hid an environment choice')
    return dict(total_relations=len(total),preimage_cases=wp_cases,associativity_cases=assoc_cases,
                partial_relation_false_pass=True,retained_outcomes=sorted(real),
                scope='finite relation law after policy/input choices are fixed; not a local-policy lift')

def accounting_obstructions():
    # Installed maximum cannot answer whether one unit of work is available.
    capacity=F(10);levels=(F(0),F(10));cost=F(1)
    affordable=[x>=cost for x in levels]
    require(affordable==[False,True] and all(x<=capacity for x in levels),'Capacity/reserve distinction missing')
    # The effort-flow pair, not its product alone, bounds either factor.
    pairs=((F(0),F(0)),(F(0),F(100)))
    powers=[e*f for e,f in pairs]
    require(powers==[0,0] and abs(pairs[1][1])>1,'Power/current obstruction missing')
    # Same instantaneous current, different retained state and continuation.
    phi=F(0);qs=(F(0),F(1));L=C=R=F(1);u=F(0)
    derivatives=[u-R*phi/L-q/C for q in qs]
    require(derivatives==[0,-1],'Current snapshot improperly became a process summary')
    # Each incident projects to loss AND an additional external effect.
    b=6;p=1;M=4
    replacement=b+(M-1)*p;additional=b+M*p
    old_margin=F(11,2500);corrected_margin=old_margin-F(1,72)
    require(replacement==9 and additional==10 and corrected_margin<0,
            'Off-body effect was erased by target-loss projection')
    # This invalidates that sufficient collar calculation, not every policy.
    same_history=[(8,2),(2,8)]
    require(all(a+b==10 for a,b in same_history),'Shared-history construction changed')
    projected_minima=(min(a for a,b in same_history),min(b for a,b in same_history))
    require(projected_minima==(2,2) and projected_minima not in same_history,
            'Independent favorable scenarios were incorrectly assembled')
    return dict(capacity=capacity,actual_levels=levels,affordable_work=affordable,
                equal_power=powers,actual_flow=[p[1] for p in pairs],
                same_current_different_phi_derivative=derivatives,
                fault_effect=dict(old_replacement_weight=replacement,actual_additional_weight=additional,
                    old_certificate_margin=old_margin,recomputed_certificate_margin=corrected_margin,
                    source_impossibility_claimed=False),
                same_histories=same_history,nonexistent_combined_favorable_witness=projected_minima)

def serial(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {k:serial(x) for k,x in v.items()}
    if isinstance(v,(tuple,list)):return [serial(x) for x in v]
    return v

def generate():
    out=dict(status='derived finite composition laws and accounting obstructions; full joint source unadmitted',
             relations=relation_laws(),accounting=accounting_obstructions())
    out['sources']={name:sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest()
                   for name in ('COMPOSITION.md','composition_model.py','BOUNDARY-FACTORIZATION.md',
                                '../DOWNSTREAM-CONTRACT.md','../ASSUMPTION-REVIEW.md')}
    return serial(out)

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=p.parse_args()
    result=generate();target=HERE/'composition_results.json'
    if args.write:target.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(json.loads(target.read_text(encoding='utf-8-sig'))==result,'Composition record differs')
    print('composition record '+('written' if args.write else 'matches'))

if __name__=='__main__':main()
