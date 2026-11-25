"""A sensor replacement can preserve zero/one flags without preserving posterior risk."""
from fractions import Fraction as F
from itertools import combinations,product
from random import Random
from posterior import sufficient,direct

def posterior_replacement(r,e,up=True):
    x,y=(1+e,1-e) if up else (1-e,1+e)
    return x*r/(x*r+y*(1-r))

def actual_replacement_family(L,S,w,e):
    r=sufficient(L,S,w)
    n=len(L)
    opts=[]
    for signs in product((-1,1),repeat=n):
        dst=[v*(1+s*e) for v,s in zip(L,signs)]
        opts.append(direct(dst,S,w))
    assert (min(opts),max(opts))==(posterior_replacement(r,e,False),posterior_replacement(r,e))

def main():
    rng=Random(503572)
    for _ in range(960):
        n=rng.randrange(2,7)
        L=[F(rng.randrange(1,11),30) for _ in range(n)]
        S=[i for i in range(n) if rng.randrange(2)]
        w=F(rng.randrange(7),10)
        e=F(rng.randrange(1,9),10)
        actual_replacement_family(L,S,w,e)
        for p in (F(1,2),F(3,2)):
            assert sufficient([p*l for l in L],S,w)==sufficient(L,S,w)
    # Same old red label, actual relative likelihood changes.
    A=(F(1,2),F(1,4),F(1,4));B=(F(1,4),F(1,2),F(1,4));S=(0,)
    assert sum(A)==sum(B)
    a,b=sufficient(A,S,F(1,4)),sufficient(B,S,F(1,4))
    assert a>F(1,2)>=b
    print('960 exhaustive bounded replacement corners; same delivered label can change approval',a,b)
if __name__=='__main__':main()
