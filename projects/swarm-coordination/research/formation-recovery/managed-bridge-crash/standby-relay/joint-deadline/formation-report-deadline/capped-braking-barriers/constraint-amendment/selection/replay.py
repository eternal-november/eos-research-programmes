#!/usr/bin/env python3
"""Compare constraint selection with directed length-bounded cut exactly."""
from collections import deque
from itertools import product
import json
import random


def violating_graph(vn,edges,L,with_bands=True):
    # Rescale every slack and debt by 4(L+1); all arithmetic is exact.
    s,t=vn,vn+1
    N=vn+2
    w=L+1
    inf=10*N*w
    d=[[inf]*N for _ in range(N)]
    speed=[1]*vn+[0,2]
    mandatory=[(s,0,w),(vn-1,t,w)]
    if with_bands:
        mandatory += [(i,i+1,4*w) for i in range(N-1)]
        mandatory += [(i+1,i,4*w) for i in range(N-1)]
    for i in range(N):
        d[i][i]=0
    for i,j,c in mandatory+[(i,j,2) for i,j in edges]:
        d[i][j]=min(d[i][j],c)
    for k in range(N):
        for i in range(N):
            dik=d[i][k]
            for j in range(N):
                if dik+d[k][j]<d[i][j]:
                    d[i][j]=dik+d[k][j]
    return any(d[i][j]<w*max(0,speed[j]-speed[i])**2
               for i,j in product(range(N),repeat=2))


def short_path(n,edges,L):
    outgoing=[[] for _ in range(n)]
    for i,j in edges:
        outgoing[i].append(j)
    seen={0}
    queue=deque([(0,())])
    while queue:
        i,p=queue.popleft()
        if i==n-1:
            return p
        if len(p)<L:
            for j in outgoing[i]:
                if j not in seen:
                    seen.add(j)
                    queue.append((j,p+((i,j),)))
    return None


def bounded(n,edges,L,B):
    p=short_path(n,edges,L)
    if p is None:
        return frozenset()
    if B==0:
        return None
    for e in p:
        sub=bounded(n,edges-{e},L,B-1)
        if sub is not None:
            return sub|{e}
    return None


def replay():
    r=random.Random(516)
    subset_checks=decision_checks=0
    for _ in range(160):
        n=r.randrange(4,8)
        L=r.randrange(2,7)
        all_edges=[(i,j) for i,j in product(range(n),repeat=2)
                   if i!=j and (i,j)!=(0,n-1)]
        es=r.sample(all_edges,r.randrange(5,10))
        m=len(es)
        best=m
        for bits in product((0,1),repeat=m):
            E={e for b,e in zip(bits,es,strict=True) if b}
            negative=violating_graph(n,list(E),L)
            assert negative == (short_path(n,E,L) is not None)
            if len(E)==1:
                assert not negative
            if not negative:
                best=min(best,m-len(E))
            subset_checks+=1
        for B in range(m+1):
            out=bounded(n,set(es),L,B)
            assert (out is not None)==(best<=B)
            if out is not None:
                assert len(out)<=B and not violating_graph(n,list(set(es)-out),L)
            decision_checks+=1
    checks=0
    for k in range(2,25):
        e={(i,i+1) for i in range(k)}
        assert violating_graph(k+1,list(e),k)
        assert not violating_graph(k+1,list(e),k-1)
        for p in e:
            assert not violating_graph(k+1,list(e-{p}),k)
            checks+=1
    greedy_checks=0
    for n in range(2,30):
        t=n+2
        common=(0,1)
        branches=[e for i in range(2,t) for e in ((1,i),(i,t))]
        accepted=set()
        for e in [common]+branches:
            if not violating_graph(t+1,list(accepted|{e}),3):
                accepted.add(e)
        assert len(accepted)==n+1
        assert not violating_graph(t+1,branches,3)
        assert violating_graph(t+1,[common]+branches,3)
        greedy_checks+=1
    return dict(subset_equivalences=subset_checks,
                budget_search_decisions=decision_checks,
                minimal_chain_conflicts=23,
                single_removal_clearances=checks,
                largest_minimal_conflict_replayed=24, greedy_controls=greedy_checks)


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
