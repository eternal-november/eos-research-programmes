"""A fixed-law, not independently reselected, posterior risk envelope."""
from fractions import Fraction as F
from itertools import combinations
from random import Random

def direct(likelihood,exposed,spike):
    n=len(likelihood);base=(1-spike)/n
    out=[]
    for j in range(n):
        weighted=[base*v+(spike*v if i==j else 0) for i,v in enumerate(likelihood)]
        out.append(sum(weighted[i] for i in exposed)/sum(weighted))
    return max(out)

def sufficient(likelihood,exposed,spike):
    A=sum((likelihood[i] for i in exposed),F(0))
    B=sum(likelihood)
    M=max((likelihood[i] for i in exposed),default=F(0))
    a=(1-spike)/len(likelihood)
    assert B>0 and a>0
    return (a*A+spike*M)/(a*B+spike*M)

def small(n,k,spike,strength):
    low=F(1)/(1+strength);high=strength*low
    sx=[tuple(high if j==i else low for i in range(n)) for j in range(n)]
    miss=sufficient(sx[n-1],tuple(range(k)),spike)
    hit=sufficient(sx[0],tuple(range(k)),spike)
    assert miss<hit
    cap=(hit+miss)/2
    # Receiver asked to decide whether the already-incurred event satisfies a
    # newly activated conditional risk cap, NOT to erase it on a failed check.
    signatures=set()
    for K in combinations(range(n),k):
        row=tuple(sufficient(L,K,spike)>cap for L in sx)
        assert row==tuple(i in K for i in range(n))
        signatures.add(row)
    from math import comb
    assert len(signatures)==comb(n,k)
    return miss,hit,cap

def main():
    rng=Random(691882)
    for j in range(3600):
        n=rng.randrange(2,18)
        ell=[F(rng.randrange(12),12) for _ in range(n)]
        if not sum(ell):ell[0]=F(1,12)
        S=[i for i in range(n) if rng.randrange(2)]
        w=F(rng.randrange(20),20)
        assert sufficient(ell,S,w)==direct(ell,S,w)
    print('3600 exact one-fixed-law-per-mission conditional-risk computations')
    for n in range(2,11):
        for k in range(1,n):
            for w in (F(0),F(1,4),F(3,4)):
                small(n,k,w,F(5,4))
    x=small(6,2,F(1,4),F(2))
    print('positive evidence can change the cap decision after identical old risk:',x)
if __name__=='__main__':main()
