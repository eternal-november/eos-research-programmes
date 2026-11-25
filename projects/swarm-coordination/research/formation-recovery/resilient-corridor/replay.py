"""Exact single-file terminal connectivity after up to k radio-only losses."""
from itertools import combinations, product
from fractions import Fraction as F
from random import Random

def required(n,k):
    return [(i,j) for i in range(n) for j in range(i+1,min(n,i+k+2))]

def spans(x,R,k):
    return all(x[j]-x[i]<=R for i,j in required(len(x),k))

def explicit(x,R,k):
    internal=list(range(1,len(x)-1))
    for p in range(min(k,len(internal))+1):
        for drop in combinations(internal,p):
            left=set(range(len(x)))-set(drop)
            active=[0];seen={0}
            for i in active:
                for j in left-seen:
                    if abs(x[j]-x[i])<=R:
                        seen.add(j);active.append(j)
            if seen!=left:return False
    return True

def upper_bounds(n,edges):
    # Floyd-Warshall is independently used as a direct known comparator.
    inf=float("inf")
    G=[[0 if i==j else inf for j in range(n+1)] for i in range(n+1)]
    for i,j,w in edges:G[i][j]=min(G[i][j],w)
    for z in range(n+1):
        for i in range(n+1):
            if G[i][z]==inf:continue
            for j in range(n+1):
                if G[z][j]!=inf:G[i][j]=min(G[i][j],G[i][z]+G[z][j])
    if any(G[i][i]<0 for i in range(n+1)):return None
    assert all(d<inf for d in G[n][:n])
    return tuple(G[n][:n])

def solver(B, pairs,g,R,lower=False):
    n=len(B)
    edges=[edge for i,(L,U) in enumerate(B) for edge in [(n,i,U),(i,n,-L)]]
    edges.extend((i+1,i,-g) for i in range(n-1))
    edges.extend((i,j,R) for i,j in pairs)
    if lower:edges=[(j,i,w) for i,j,w in edges]
    res=upper_bounds(n,edges)
    if res is None:return None
    return tuple(-x for x in res) if lower else res

def placement(x,speeds,body,cut,T,g,R,k,lens_block=()):
    bounds=[]
    for i,(a,v) in enumerate(zip(x,speeds)):
        l,u=a-v*T,a+v*T
        if i<cut:u=min(u,body-g)
        else:l=max(l,body+g)
        if i in lens_block:l,u=max(l,x[-1]-R),min(u,x[0]+R)
        bounds.append((l,u))
    n=len(x)
    pairs=required(n,k)
    left=solver(bounds[:cut],[(i,j) for i,j in pairs if j<cut],g,R)
    right=solver(bounds[cut:],[(i-cut,j-cut) for i,j in pairs if i>=cut],g,R,True)
    can=None if left is None or right is None else left+right
    if can is not None and not spans(can,R,k):can=None
    full=solver(bounds,pairs,g,R)
    assert (can is not None)==(full is not None)
    if can is not None:
        assert all(L<=i<=U for (L,U),i in zip(bounds,can))
        assert all(b-a>=g for a,b in zip(can,can[1:]))
        assert can[cut-1]+g<=body<=can[cut]-g
    return can,tuple(bounds)

def lattice():
    rng=Random(25112026)
    for case in range(10000):
        n=rng.randrange(2,10);cut=rng.randrange(1,n)
        x=[0]
        for _ in range(n-1):x.append(x[-1]+rng.randrange(2,7))
        body=F(x[cut-1]+x[cut],2)
        v=[0]+[rng.randrange(1,4) for _ in range(n-2)]+[0]
        k,R,T=rng.randrange(n),rng.randrange(1,15),F(rng.randrange(7),2)
        L,_=placement(x,v,body,cut,T,1,R,k)
        assert L is None or explicit(L,R,k)
    samples=0
    for n in range(2,9):
        for gaps in product(range(1,4),repeat=n-1):
            x=[0]
            for a in gaps:x.append(x[-1]+a)
            for k,R in product(range(n-1),range(1,6)):
                assert spans(x,R,k)==explicit(x,R,k),(x,R,k)
                samples+=1
    print(samples,"explicit radio removal comparisons")
    print("10000 exact rational split versus global constraint comparisons")

def physical():
    x=(0,1,2,6,7,8);v=(0,1,1,1,1,0)
    assert placement(x,v,4,3,0,1,4,0)[0]
    assert placement(x,v,4,3,F(49,100),1,4,1)[0] is None
    y,_=placement(x,v,4,3,F(1,2),1,4,1)
    assert y==(0,F(3,2),F(5,2),F(11,2),F(13,2),8)
    print("exact terminal robustness deadline 1/2 from span 5, relative speed at most 2")
    print("first robust placement",y)

def probes():
    # At every tested cut, any full-span crossing pair can break alone,
    # so a truthful one-bit link tester must query all such pairs on the
    # all-pass history if it has no stronger location evidence.
    count=0;d=F(1,12)
    for n in range(3,14):
        for cut in range(1,n):
            body=F(2*cut-1,2)
            for q in range(1,n):
                R=q+F(3,2)*d
                base=tuple(range(n))
                assert spans(base,R,q-1)
                for i in range(n-q):
                    j=i+q
                    if not i<cut<=j:continue
                    # Fixed anchors can be at boundary. If a single anchor
                    # appears in target, both perturbations are not allowed;
                    # this lower-bound family uses strictly interior endpoints.
                    if i==0 or j==n-1:continue
                    alt=list(base);alt[i]-=d;alt[j]+=d
                    assert all(b-a>=F(1,3) for a,b in zip(alt,alt[1:]))
                    assert alt[cut-1]+F(1,3)<=body<=alt[cut]-F(1,3)
                    broken=[(u,v) for u,v in required(n,q-1) if alt[v]-alt[u]>R]
                    assert broken==[(i,j)],(broken,i,j)
                    flips=[(u,v) for u,v in combinations(range(n),2)
                           if (alt[v]-alt[u]<=R)!=(base[v]-base[u]<=R)]
                    assert flips==[(i,j)]
                    count+=1
    print(count,"single-bit cross-link indistinguishability witnesses")

if __name__=="__main__":
    physical();probes();lattice()
