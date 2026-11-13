#!/usr/bin/env python3
"""Independent H=2 exact enumeration of robust recursive-prediction bound.
Exploration is fair-action. Evidence family is convex hull of two persistent
world laws. Predictor stores previous observed bit and has a fixed four-row
response table reused under every controller.
"""
from fractions import Fraction as F
from itertools import product
import json
H=2
records=list(product((0,1),repeat=4)) # a0,o1,a1,o2, fixed o0=0
worlds=(F(1,4),F(3,4))
def bern(x,p): return p if x else 1-p
def world(theta):
    return {r:F(1,4)*bern(r[1],theta if r[0]==0 else 1-theta)*bern(r[3],theta if r[2]==0 else 1-theta) for r in records}
P0,P1=map(world,worlds)
def mixture(alpha): return {r:alpha*P0[r]+(1-alpha)*P1[r] for r in records}
def policy(bits):
    return {( ):F(bits[0]),**{(a,o):F(bits[1+2*a+o]) for a,o in product((0,1),repeat=2)}}
policies=[policy(b) for b in product((0,1),repeat=5)]
def eval_pair(p,pi,K):
    # Policy weighting preserves one fixed p over the whole trajectory.
    true={r:4*p[r]*bern(r[0],pi[()])*bern(r[2],pi[r[:2]]) for r in records}
    pred={r:bern(r[0],pi[()])*bern(r[1],K[0,r[0]])*bern(r[2],pi[r[:2]])*bern(r[3],K[r[1],r[2]]) for r in records}
    assert sum(true.values())==sum(pred.values())==1
    delta=sum(abs(true[r]-pred[r]) for r in records)/2
    J=F(0)
    for t in (0,1):
        for prefix in product((0,1),repeat=2*t):
            for a in (0,1):
                matching=[r for r in records if r[:2*t]==prefix and r[2*t]==a]
                ep=sum(p[r] for r in matching)
                ep1=sum(p[r] for r in matching if r[2*t+1])
                tp=sum(true[r] for r in matching)
                assert ep>0
                last=0 if not prefix else prefix[-1]
                J+=tp*abs(ep1/ep-K[last,a])
    assert delta<=min(F(1),J)
    assert J<=(2*H+1)*delta
    assert (delta==0)==(J==0)
    return J,delta
ks=[]
for vals in product((F(1,4),F(1,2),F(3,4)),repeat=4):
    ks.append(dict(zip(product((0,1),repeat=2),vals)))
checks=0; convex_checks=0; policy_checks=0
for K in ks:
    j0=[eval_pair(P0,pi,K)[0] for pi in policies]
    j1=[eval_pair(P1,pi,K)[0] for pi in policies]
    checks+=2*len(policies)
    for alpha in (F(1,4),F(1,2),F(3,4)):
        p=mixture(alpha)
        js=[]
        for i,pi in enumerate(policies):
            j,d=eval_pair(p,pi,K)
            assert j<=alpha*j0[i]+(1-alpha)*j1[i]
            js.append(j); checks+=1; convex_checks+=1
        for action_prob in (F(1,4),F(1,2),F(3,4)):
            pi={h:action_prob for h in policies[0]}
            j,d=eval_pair(p,pi,K)
            assert j<=max(js)
            checks+=1; policy_checks+=1
print(json.dumps({"status":"PASS","horizon":H,"recursive_predictor_tables":len(ks),
 "deterministic_full_history_policies":len(policies),"bound_checks":checks,
 "confidence_law_convexity_checks":convex_checks,"randomized_policy_extremality_checks":policy_checks,
 "scope":"Finite exact regression, not formal proof or exhaustive general validation"},indent=2))
