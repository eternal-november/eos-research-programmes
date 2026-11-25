"""Shared/independent randomness at the same admitted source support."""
from selector import *
from fractions import Fraction as F
from math import inf

def distances(S):
    V=tuple((i,j) for i,rows in enumerate((S.left,S.right)) for j in range(len(rows)))
    pins={}
    adj={v:[] for v in V}
    for i,j in S.edges:
        a,b=(0,i),(1,j)
        adj[a].append(b);adj[b].append(a)
    for k,v in V:
        lst=(S.left,S.right)[k][v]
        assert lst
        if len(lst)==1:pins[(k,v)]=lst[0]^k
    d={v:0 for v in V if pins.get(v)==0};q=deque(d)
    while q:
        v=q.popleft()
        for w in adj[v]:
            if w not in d:d[w]=d[v]+1;q.append(w)
    l=min((d.get(v,inf) for v,b in pins.items() if b),default=inf)
    return d,l,pins

def pub(S):
    d,l,pins=distances(S)
    if l==inf:
        pay,w=solve(S)
        assert pay is not None
        return [pay],F(1)
    assert l>=1
    C=[]
    V=tuple((i,j) for i,rows in enumerate((S.left,S.right)) for j in range(len(rows)))
    for k in range(l):
        m={v:int(d.get(v,inf)>k)^v[0] for v in V}
        assert all(m[v]==w^v[0] for v,w in pins.items())
        C.append(m)
    return C,F(l-1,l)

def score(S,policies):
    probs=[sum(m[0,i]!=m[1,j] for m in policies) for i,j in S.edges]
    return min((F(p,len(policies)) for p in probs),default=F(1))

def exact_lp(S):
    # Matched small finite randomized policy baseline, using SciPy HiGHS.
    import numpy as np
    from scipy.optimize import linprog
    if not S.edges:return 1
    L=tuple(product(*S.left));R=tuple(product(*S.right))
    p=tuple(product(L,R));d=len(p)
    c=np.zeros(d+1);c[-1]=-1
    W=np.array([[int(m[0][i]==m[1][j])-1 for m in p]+[1] for i,j in S.edges],dtype=float)
    s=linprog(c,A_ub=W,b_ub=np.zeros(len(S.edges)),A_eq=np.array([[1]*d+[0]]),b_eq=[1],bounds=(0,1),method='highs')
    assert s.success
    return -s.fun

def main():
    rng=Random(182)
    for n in range(1,81):
        S=path(n)
        p,q=pub(S)
        assert len(p)==n
        assert score(S,p)==q==F(n-1,n)
    states=((0,),(1,),(0,1))
    k=0;solved=0
    for n in range(1,6):
        for _ in range(110):
            E=tuple(e for e in product(range(n),repeat=2) if rng.random()<.37)
            S=Source(E,tuple(rng.choice(states) for _ in range(n)),tuple(rng.choice(states) for _ in range(n)))
            p,q=pub(S)
            assert score(S,p)==q
            if n<=4 and (_%9==0):
                assert abs(exact_lp(S)-float(q))<1e-9
                solved+=1
            k+=1
    # Independent fair bits for all unpinned labels achieve success 1/2
    # whenever no source edge has two incompatible pins. For necessity
    # follow an opposite-pin path and choose a crossing of 1/2.
    from itertools import pairwise
    for t in product((F(0), F(1,4), F(1,2), F(3,4), F(1)),repeat=5):
        q=(F(0),*t,F(1))
        assert any(a+b-2*a*b>=F(1,2) for a,b in pairwise(q))
    print(k,'exact rational public-seed policy checks;',solved,'small matched LP solutions')
    print('sharp shared success 1-1/d for shortest incompatible pin path d')
    print('independent success capped at 1/2 for d>=2; d=1 is physically infeasible')
if __name__=='__main__':main()
