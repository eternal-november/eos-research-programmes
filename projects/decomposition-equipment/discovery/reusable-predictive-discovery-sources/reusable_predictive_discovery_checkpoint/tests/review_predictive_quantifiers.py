#!/usr/bin/env python3
"""Exact rational regression tests for predictive-discovery scope errors.
Independent reviewer tests; these establish counterexamples, not the main theorem.
"""
from fractions import Fraction as F
from itertools import product
import json

def tv(p,q):
    return sum(abs(p.get(x,F(0))-q.get(x,F(0))) for x in set(p)|set(q))/2

def bern_word(w,p):
    ans=F(1)
    for x in w: ans*=p if x else 1-p
    return ans

# A persistent uncertain parameter is not a rectangular uncertainty set.
worlds=(F(1,4),F(3,4))
checks=0
for t in range(5):
    for h in product((0,1),repeat=t):
        for p in worlds:
            assert bern_word(h,p)>0
            assert bern_word(h+(1,),p)/bern_word(h,p)==p
            checks+=1
fixed_disagreement=[]
for p in worlds:
    fixed_disagreement.append(sum(bern_word(w,p) for w in ((0,1),(1,0))))
assert fixed_disagreement==[F(3,8),F(3,8)]
rect={}
for x,y in product((0,1),repeat=2):
    p1=F(1,4)
    p2=F(3,4) if x==0 else F(1,4)
    rect[x,y]=(p1 if x else 1-p1)*(p2 if y else 1-p2)
assert sum(rect.values())==1
assert rect[0,1]+rect[1,0]==F(3,4)

# Persistent shared parity is invisible to each whole marginal process.
T=4
persistent={}; fresh={}
for xs in product((0,1),repeat=T):
    for ys in product((0,1),repeat=T):
        parity=tuple(x^y for x,y in zip(xs,ys))
        persistent[xs,ys]=F(1,2**(T+1)) if len(set(parity))==1 else F(0)
        fresh[xs,ys]=F(1,2**(2*T))
assert sum(persistent.values())==sum(fresh.values())==1
for xs in product((0,1),repeat=T):
    assert sum(v for (x,y),v in persistent.items() if x==xs)==F(1,2**T)
    assert sum(v for (x,y),v in fresh.items() if x==xs)==F(1,2**T)
for ys in product((0,1),repeat=T):
    assert sum(v for (x,y),v in persistent.items() if y==ys)==F(1,2**T)
    assert sum(v for (x,y),v in fresh.items() if y==ys)==F(1,2**T)
assert tv(persistent,fresh)==1-F(1,2**(T-1))

# Tiny joint-law error permits maximal error conditional on a rare event.
for k in range(2,20):
    eps=F(1,2**k)
    p={(0,0):1-eps,(1,0):eps}
    q={(0,0):1-eps,(1,1):eps}
    assert tv(p,q)==eps
    cp={0:F(1),1:F(0)}; cq={0:F(0),1:F(1)}
    assert tv(cp,cq)==1

# A policy-supported observation law does not identify unused actions.
# Worlds have deterministic readout next: f0(a)=0 and f1(a)=a.
for a in (0,1):
    f0=0; f1=a
    assert (f0==f1)==(a==0)

# Agreement through each prescribed finite H does not certify longer reuse.
for H in range(1,20):
    all_zero=(0,)*(H+1)
    late_change=(0,)*H+(1,)
    assert all_zero[:H]==late_change[:H]
    assert all_zero!=late_change

result={"status":"PASS","conditional_common_parameter_checks":checks,
        "fixed_world_disagreement":"3/8","rectangularized_disagreement":"3/4",
        "persistent_vs_fresh_joint_TV_T4":str(tv(persistent,fresh)),
        "rare_history_cases":18,"finite_horizon_nonextension_cases":19,
        "scope":"Counterexample regressions only; not main theorem verification"}
print(json.dumps(result,indent=2))
