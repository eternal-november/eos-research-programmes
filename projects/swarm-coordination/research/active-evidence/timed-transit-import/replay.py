from macro import *
from import_topology import matrix
from itertools import product
from random import Random
from fractions import Fraction as F

def test_windows():
    n=0
    # Physical half-open outages across actual staggered edge placements.
    P=tuple(range(5))
    for ds,i,lo,width in product(product(range(1,4),repeat=4),range(4),range(10),range(1,4)):
        D=dict(zip(zip(P,P[1:]),ds));U={(i,i+1):[(lo,lo+width)]}
        d,W=forbidden(P,D,U)
        assert d==sum(ds)
        for t in range(16):
            assert can_enter(t,W)==physical(P,D,U,t),(ds,i,lo,width,t)
            n+=1
    print(n,"pointwise staggered occupancy comparisons")
    P=(0,1,2);D={(0,1):2,(1,2):2};U={(1,2):[(0,2)]}
    _,W=forbidden(P,D,U)
    assert can_enter(0,W) and physical(P,D,U,0)
    print("an outage before reaching an internal tile does not close the whole route")
    U={(1,2):[(2,3)]};_,W=forbidden(P,D,U)
    assert not can_enter(0,W) and physical(P,D,U,1)
    print("an open-at-launch tile can be unavailable exactly when reached")

def no_shortcut_controls(A,C,pin,tag,out,dur,st,go,H=60):
    tests=[]
    for x,p in enumerate(C):
        D,B=forbidden(p,dur,out)
        assert D==sum(dur[a,b] for a,b in zip(p,p[1:]))
        tests.append((D,B))
    hit=shortest(0,C,tests,st,go,H)
    # Independent reference search: pointwise time and actual constituent
    # arcs. At non-landmarks the trajectory is committed and has no choice.
    arcs=defaultdict(list)
    for p in C:arcs[p[0]].append(p)
    S={(st,0)};result=None
    for t in range(H+1):
        for u in {u for u,q in S if q==t}:
            if u==go:
                result=t;break
            S.add((u,t+1))
            for p in arcs[u]:
                if physical(p,dur,out,t):
                    S.add((p[-1],t+sum(dur[a,b] for a,b in zip(p,p[1:]))))
        if result is not None:break
    assert hit==result,tag
    return hit

def graph_ref():
    A=development_cells()
    # Development labels deterministically fixed before evaluating outcomes.
    # Do not use this already viewed source for independent acceptance.
    s=min(A);g=max(A)
    pins,C=chains(A,{s,g})
    C=C+[tuple(reversed(e)) for e in C]
    dur={(a,b):1 for a in A for b in A[a]}
    rng=Random(332)
    candidates=sorted(dur)
    for trial in range(80):
        out={e:[(t,t+q)] for e,t,q in
             [(rng.choice(candidates),rng.randrange(15),rng.randrange(1,6)) for _ in range(4)]}
        no_shortcut_controls(A,C,pins,trial,out,dur,s,g)
    baseline=no_shortcut_controls(A,C,pins,80,{},dur,s,g,70)
    strict=no_shortcut_controls(A,C,pins,81,{(s,x):[(0,5)] for x in A[s]},dur,s,g,70)
    assert baseline==57 and strict==62
    print(len(A),"development tiles ->",len(pins),"control cuts and",len(C),"directed transit actions")
    print("82 development graph outage comparisons; closure at the start shifts earliest arrival 57 to 62")

if __name__=="__main__":test_windows();graph_ref()
