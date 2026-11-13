#!/usr/bin/env python3
"""Independent exact tests of service example and source-support claims."""
from fractions import Fraction as F
from itertools import product,combinations
import json
rows=list(product((0,1),repeat=6))
outs=list(product((0,1),repeat=2))
P={}; marg={}
for c in rows:
    y0,y1,z0,z1,a0,a1=c
    p=F(1+3*a0+2*z0+2*y1,10)
    q=F(1+3*a1+2*z1+2*y0,10)
    b=(p*q+min(p,q))/2
    P[c]={(0,0):1-p-q+b,(0,1):q-b,(1,0):p-b,(1,1):b}
    assert sum(P[c].values())==1 and min(P[c].values())>0
    marg[c]=(p,q)
scopes=[]
for i in (0,1):
    passing=[]
    for mask in range(64):
        grouped={}; ok=True
        for c in rows:
            key=tuple(c[j] for j in range(6) if mask>>j&1)
            if key in grouped and grouped[key]!=marg[c][i]: ok=False
            grouped[key]=marg[c][i]
        if ok: passing.append(mask)
    minimal=[m for m in passing if not any(k!=m and k&m==k for k in passing)]
    scopes.append((passing,minimal))
assert scopes[0][1]==[22] and scopes[1][1]==[41]
assert len(scopes[0][0])==len(scopes[1][0])==8
# Independent implementation enumeration, including all counterfactual contexts.
atoms=[(u,u,F(1,20)) for u in range(10)]
atoms += [(u,v,F(1,200)) for u,v in product(range(10),repeat=2)]
for c in rows:
    p,q=marg[c]
    rebuilt={o:F(0) for o in outs}
    for u,v,w in atoms:
        rebuilt[int(F(u,10)<p),int(F(v,10)<q)]+=w
    assert rebuilt==P[c]
max_tv=max(sum(abs(P[c][x,y]-(marg[c][0] if x else 1-marg[c][0])*(marg[c][1] if y else 1-marg[c][1])) for x,y in outs)/2 for c in rows)
assert max_tv==F(1,4)
# W product-support lower bound: nonnegative factors cannot cancel forbidden mass.
W={(1,0,0),(0,1,0),(0,0,1)}
nonempty=[(0,),(1,),(0,1)]
allowed=[]
for ss in product(nonempty,repeat=3):
    support=set(product(*ss))
    if support<=W: allowed.append(support)
assert len(allowed)==3 and all(len(s)==1 for s in allowed)
assert not any(set.union(*p)==W for p in combinations(allowed,2))
assert set.union(*allowed)==W
# Coarse AB|C admits exactly the two rectangles used by binary shared source.
assert {((1,0),0),((0,1),0)} | {((0,0),1)} == {((a,b),c) for a,b,c in W}
# Filter derivative bound: denominator-x = .09(x-1)^2, rational regression.
for k in range(1,201):
    x=F(k,17)
    denominator=F(9,100)+F(82,100)*x+F(9,100)*x*x
    assert denominator-x==F(9,100)*(x-1)**2
    assert F(4,5)*x/denominator<=F(4,5)
p=F(1,2)
seen=set()
for _ in range(40):
    assert p not in seen
    seen.add(p)
    new=(4+32*p)/(13+24*p)
    assert p<new<1
    p=new
print(json.dumps({"status":"PASS","contexts":64,"source_atoms":110,
 "minimal_scope_masks":[22,41],"passing_masks_per_port":8,
 "maximum_independent_marginal_TV":str(max_tv),
 "W_fine_support_rectangles":len(allowed),"filter_derivative_checks":200,
 "distinct_posterior_checks":40,
 "scope":"Exact synthetic example and static source bounds; no finite-log discovery or general theorem validation"},indent=2))
