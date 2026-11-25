"""Exact timed custody/observation audit for calibrated source constraints."""
from dataclasses import dataclass
from itertools import product
from math import inf
from random import Random

# Every arc (u,v,b) asserts T[v]-T[u] <= b.
def fixed(u,v,b):return ((u,v,b),(v,u,-b))
def interval(u,v,lo,hi):return ((u,v,hi),(v,u,-lo))
def neg(edge):
    u,v,b=edge
    return v,u,-b-1  # exact integer negation

def close(n,arcs):
    D=[[inf]*n for _ in range(n)]
    for u in range(n):D[u][u]=0
    for u,v,b in arcs:D[u][v]=min(D[u][v],b)
    for k in range(n):
        for i in range(n):
            for j in range(n):D[i][j]=min(D[i][j],D[i][k]+D[k][j])
    return D

def vertex_witness(n,arcs):
    # Bellman-Ford from an implicit zero-valued fresh root.
    p=[0]*n
    for _ in range(n):
        changed=False
        for u,v,b in arcs:
            if p[u]+b<p[v]:
                p[v]=p[u]+b;changed=True
        if not changed:
            p=[q-p[0] for q in p]
            assert all(p[v]-p[u]<=b for u,v,b in arcs)
            return p
    return None

def bad(n,arcs,routes):
    # For each acceptable route, choose the physical or availability
    # inequality that fails. A jointly possible failure tuple refutes
    # a universal existential claim, using one assignment to ALL clocks.
    for probes in product(*routes):
        A=tuple(arcs)+tuple(map(neg,probes))
        D=close(n,A)
        w=vertex_witness(n,A)
        assert (w is None)==any(D[i][i]<0 for i in range(n))
        if w is not None:return w
    return None

def specimen(cut):
    # nodes: epoch, station offset, A pickup attempt, A fault,
    # B pickup attempt, B fault, A/B receipt, deciding actor's cut.
    A=fixed(1,2,0)+fixed(0,3,0)
    B=fixed(0,4,0)+fixed(1,5,1)
    arcs=interval(0,1,-1,1)+A+B
    arcs+=interval(2,6,1,2)+interval(4,7,1,2)+fixed(0,8,cut)
    # pickup must be strictly before fault; arrival may be at decision time
    pa,pb=(3,2,-1),(5,4,-1)
    ra,rb=(8,6,0),(8,7,0)
    return arcs,((pa,),(pb,)),((pa,ra),(pb,rb))

def applies(w,rail):
    return all(w[v]-w[u]<=b for u,v,b in rail)

def main():
    arcs,P,R=specimen(1)
    assert bad(9,arcs,P) is None
    assert all(bad(9,arcs,(g,)) is not None for g in P)
    w=bad(9,arcs,R)
    assert w is not None and not any(applies(w,t) for t in R)
    assert bad(9,*[specimen(2)[i] for i in (0,2)]) is None
    print('correlated clocks guarantee one captured item, but neither fixed item is guaranteed')
    print('cut 1 may have no timely positive receipt; cut 2 guarantees at least one')
    rng=Random(42017); ntests=0
    for q in range(550):
        n=4;A=[]
        for x in range(1,n):A+=interval(0,x,-2,2)
        for it in range(rng.randrange(6)):
            a,b=rng.sample(range(n),2);A.append((a,b,rng.randint(-2,3)))
        # Empty base support is an invalid evidence packet, not a guarantee.
        if vertex_witness(n,A) is None:continue
        r=tuple(tuple((*rng.sample(range(n),2),rng.randrange(-2,4))
                    for _ in range(rng.randrange(1,3))) for m in range(rng.randrange(1,4)))
        w=bad(n,A,r)
        D=[(0,*m) for m in product(range(-2,3),repeat=n-1)]
        fail=[s for s in D if applies(s,A) and not any(applies(s,z) for z in r)]
        assert (w is None)==(not fail)
        if w is not None:assert tuple(w) in fail
        ntests+=1
    print(ntests,'clock systems agree with independent exhaustive integer-time checks')
if __name__=='__main__':main()
