#!/usr/bin/env python3
"""Independent integer-tick ledger model and exact two-by-two risk analysis."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import json, sys

def direct(k, sx, sy, a):
    c, x, o, gap, size = k
    history = []
    def accept(t,n):
        if n + sum(b for s,b in history if 0<=t-s<=16)>c:
            return 0
        history.append((t,n))
        return 1
    y=int(sy and accept(0,1))
    xout=int(sx and accept(x,2))
    opt=int(a and accept(o,size))
    redo=accept(o+gap,2)
    return (xout,y,opt,redo,1,int(y or redo))

ks=list(product((2,3,4,5),(1,2,3),(15,16,17,18),(1,2,3),(1,2,3)))
cases = set(product(ks, *((0,1),)*3))
base={}
for line in open(sys.argv[1], encoding='utf-8'):
    c,x,o,g,b,sy,sx,a,*out=map(int,line.split())
    k=(c,x,o,g,b)
    case=(k,sx,sy,a)
    cases.remove(case)
    assert direct(*case)==tuple(out),(case,out)
    base[case]=tuple(out)
assert not cases
K=((0,0),(0,1),(1,0),(1,1))
def witnesses(k):
    E=defaultdict(set)
    for sx,sy in product((0,1),repeat=2):
        off=base[k,sx,sy,0]
        on=base[k,sx,sy,1]
        assert off[:2]==on[:2] and off[4]==on[4]==1
        increment=int(off[-1] and not on[-1])
        baseline_loss=1-off[-1]
        E[on[:2]].add((baseline_loss,increment,on[2]))
    return E

def weights(p,q,t):  # probability of (row 1, column 1) is t
    return (1-p-q+t,q-t,p-t,t)

def endpoints(E,p,q):
    lo=max(0,p+q-1)
    hi=min(p,q)
    for z,zero in zip(K,(p+q-1,q,p,0)):
        if z not in E:
            lo=max(lo,zero)
            hi=min(hi,zero)
    return () if lo>hi else (lo,hi)

def objective(w,c):
    return sum(a*b for a,b in zip(w,c))

all_pairs = set(K)
focal={}
for c in (2,3):
    E=witnesses((c,1,17,1,2))
    assert all(len(v)==1 for v in E.values())
    marks={e:next(iter(v)) for e,v in E.items()}
    assert marks=={e:(0,int(e==(0,0)),int(e[0]==0)) for e in marks}
    assert set(marks)==all_pairs-({(1,1)} if c==2 else set())
    p=q=Q(1,2)
    full=[weights(p,q,t) for t in endpoints(E,p,q)]
    value=max(objective(w,(1,0,0,0)) for w in full)
    u=(1,0)
    v=(0,-1) if c==2 else (0,0)
    assert all(u[i]+v[j]>=int(i==j==0) for i,j in E)
    assert (u[0]+u[1]+v[0]+v[1])*p==value
    focal[c]={"support":["".join(map(str,e)) for e in sorted(E)],
              "worst_always_admit":str(value),
              "verified_marginal_pairs":0}
    for pnum,qnum in product(range(17),repeat=2):
        p,q=Q(pnum,16),Q(qnum,16)
        feasible=[]
        for z in range(17):
            w=weights(p,q,Q(z,16))
            if min(w)>=0 and all(w[j]==0 for j,e in enumerate(K) if e not in E):
                feasible.append(w)
        ends=endpoints(E,p,q)
        assert bool(ends)==bool(feasible)==(c==3 or p+q<=1)
        if ends:
            vmax=max(weights(p,q,t)[0] for t in ends)
            assert vmax==max(w[0] for w in feasible)
            assert vmax==(1-p-q if c==2 else 1-max(p,q))
        focal[c]["verified_marginal_pairs"]+=1
# Both time cuts are material: one tick earlier, Y is still charged;
# one tick later, X has also expired, so row X=1 can lose its old retry.
earlier=witnesses((2,1,16,2,2))
later=witnesses((2,1,18,1,2))
assert earlier[0,1]=={(0,0,0)}
assert later[1,0]=={(0,1,1)}

print(json.dumps({"native_rows":len(base),"baseline_configurations":len(ks),
 "support_sizes":{str(n):sum(len(witnesses(k))==n for k in ks) for n in (3,4)},
 "focal":focal,"phase_boundary_checks":2},indent=2,sort_keys=True))
