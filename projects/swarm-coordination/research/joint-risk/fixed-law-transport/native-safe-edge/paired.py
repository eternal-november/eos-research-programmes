#!/usr/bin/env python3
"""Paired source comparison for #851 and independent exact finite-mass sweep."""
from itertools import product
import sys
import json
from collections import defaultdict
focal={}
for row in open(sys.argv[1],encoding="utf-8"):
    c,x,t,g,s,v,u,on,X,Y,O,R,A,J=map(int,row.split())
    if c in (2,3) and (x,t,g,s)==(1,17,1,2):
        key=(c,u,v,on)
        assert key not in focal
        focal[key]=(X,Y,O,R,A,J)
assert len(focal)==16
pairs=[]
for u,v in product((0,1),repeat=2):
    pair=[]
    for c in (2,3):
        off=focal[c,u,v,0]
        on=focal[c,u,v,1]
        obs=(u*(1-v),v) if c==2 else (u,v)
        assert on[:2]==off[:2]==obs
        assert off[-1]==1 and 1-on[-1]==int(not u and not v)
        assert off[-2]==on[-2]==1
        assert on[2]==1-obs[0]
        pair.append((obs, on[2], 1-on[-1]))
    pairs.append((u,v,pair))

def interval(N,p,q,P,Q,budget):
    if p+q>N or abs(Q-q)>budget:
        return None
    d,e=P-p,Q-q
    lo=max(0,P+Q-N,d-budget,d+e-budget)
    hi=min(P,Q,d+budget,d+e+budget)
    return None if lo>hi else (lo,hi)

def mass(N):
    for a in range(N+1):
        for b in range(N+1-a):
            for c in range(N+1-a-b):
                yield a,b,c,N-a-b-c

def variation(l,r):
    return sum(abs(a-b) for a,b in zip(l,r))//2

N=16
laws=list(mass(N))
cost={}
count=0
for l,r in product(laws,repeat=2):
    a,b,p,s=l
    A,B,C,t=r
    q=b+s
    P=C+t
    Q=B+t
    k=p,q,P,Q,t
    v=variation(l,r)
    cost[k]=min(cost.get(k,N+1),v)
    count+=1
groups=defaultdict(list)
for (p,q,P,Q,t),v in cost.items():
    assert v==max(abs(t-(P-p)-(Q-q)), abs((P-p)-t),abs(Q-q))
    groups[p,q,P,Q].append((t,v))
intervals=0
for p,q,P,Q in product(range(N+1),repeat=4):
    t_cost=groups.get((p,q,P,Q),())
    for budget in range(N+1):
        attainable=sorted(t for t,v in t_cost if v<=budget)
        ans=interval(N,p,q,P,Q,budget)
        assert attainable==([] if ans is None else list(range(ans[0],ans[1]+1)))
        intervals+=1
        if ans is not None:
            assert max(N-P-Q+t for t in attainable)==N-P-Q+ans[1]
for budget in range(N+1):
    assert interval(N,8,8,8,8,budget)==(0,min(budget,8))
print(json.dumps({"source_pairs":pairs,"raw_laws_per_config":len(laws),
                  "raw_law_pairs":count,"interval_checks":intervals},sort_keys=True))
