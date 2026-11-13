#!/usr/bin/env python3
"""Exact-rational regression checks, not a proof of unknown-model discovery."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

def rank(rows):
    a=[list(r) for r in rows]
    if not a:return 0
    i=0
    for j in range(len(a[0])):
        p=next((p for p in range(i,len(a)) if a[p][j]),None)
        if p is None:continue
        a[i],a[p]=a[p],a[i]
        q=a[i][j];a[i]=[v/q for v in a[i]]
        for k in range(len(a)):
            if k!=i:
                q=a[k][j];a[k]=[v-q*w for v,w in zip(a[k],a[i])]
        i+=1
        if i==len(a):break
    return i

def closure(generators):
    basis=[tuple(F(1) for _ in generators[0])]
    dims=[]
    while True:
        old=len(basis)
        for g in generators:
            for b in list(basis):
                v=tuple(x*y for x,y in zip(g,b))
                if rank(basis+[v])>len(basis):basis.append(v)
        dims.append(len(basis))
        if len(basis)==old:return basis,dims

def avg(v):return sum(v,F(0))/len(v)
f=tuple(map(F,['.2','.2','.8','.8']))
g=tuple(map(F,['.2','.8','.2','.8']))
alg_basis,ds=closure([f,g]);assert len(alg_basis)==4
b1,_=closure([f]);assert len(b1)==2
k=tuple(x-F(1,2) for x in f)
assert avg(k)==0 and avg([x*x for x in k])==F(9,100)
f0=(F(1,2),)*4
assert avg(f)==avg(f0)
assert avg([x*x for x in f])-avg([x*y for x,y in zip(f0,f)])==F(9,100)
# Positive source alternatives agree on singleton channels, not joint product.
pplus=(F(3,8),F(1,8),F(1,8),F(3,8))
pminus=(F(1,8),F(3,8),F(3,8),F(1,8))
for h in [(F(1),)*4,f,g]:assert sum(p*x for p,x in zip(pplus,h))==sum(p*x for p,x in zip(pminus,h))
h=tuple(x*y for x,y in zip(f,g))
assert sum(p*x for p,x in zip(pplus,h))!=sum(p*x for p,x in zip(pminus,h))
# Positive HMM sequence law, stationary hidden sign.
def hmm(a,lam,ys):
    total=F(0)
    for zs in product([-1,1],repeat=len(ys)):
        p=F(1,2)
        for t,(z,y) in enumerate(zip(zs,ys)):
            p*= (1+a*z*y)/2
            if t:p*= (1+lam*zs[t-1]*z)/2
        total+=p
    return total
worlds=[(F(2,5),F(5,8)),(F(4,5),F(5,32))]
for a,lam in worlds:
    assert a*a*lam==F(1,10)
    for n in range(1,6):assert sum(hmm(a,lam,ys) for ys in product([-1,1],repeat=n))==1
    for lag in [1,2,3]:
        got=sum(ys[0]*ys[-1]*hmm(a,lam,ys) for ys in product([-1,1],repeat=lag+1))
        assert got==a*a*lam**lag
for ys in product([-1,1],repeat=2):assert hmm(*worlds[0],ys)==hmm(*worlds[1],ys)
assert any(hmm(*worlds[0],ys)!=hmm(*worlds[1],ys) for ys in product([-1,1],repeat=3))
# Hidden sign relabeling transports emission a -> -a, leaves symmetric Q unchanged.
for ys in product([-1,1],repeat=4):assert hmm(*worlds[0],ys)==hmm(-worlds[0][0],worlds[0][1],ys)
# Shared mode, independently emitted components.
aligned=sum((F(1,2)*(p*p+(1-p)*(1-p))) for p in [F(1,5),F(4,5)])
reversed_=sum((F(1,2)*(p*(1-p)+(1-p)*p)) for p in [F(1,5),F(4,5)])
assert aligned==F(17,25) and reversed_==F(8,25)
# Pointwise triangle obstruction, not an LP solver claim.
for a,b,c in product([0,1],repeat=3):assert int(a!=c)<=int(a!=b)+int(b!=c)
assert F(19,20)>F(1,20)+F(1,20)
# Fixed-world vs rectangular selection.
fixed=max((1-t)*t for t in [F(1,10),F(9,10)])
rect=(1-F(1,10))*F(9,10)
assert fixed==F(9,100) and rect==F(81,100)
result={"status":"PASS","arithmetic":"exact rational","scope":"finite regression checks; no data-learning implementation","response_algebra_dimension":len(alg_basis),"one_generator_effect_dimension":len(b1),"closure_dimensions":ds,"assembly_square_gap":str(avg([x*x for x in k])),"aligned_agreement":str(aligned),"reversed_agreement":str(reversed_),"positive_hmm_worlds":[[str(x) for x in w] for w in worlds],"lag2_correlations":[str(a*a*l*l) for a,l in worlds],"fixed_world_01":str(fixed),"rectangular_01":str(rect)}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
