"""End-to-end single-report service. Anchor endpoints never fail."""
from deadline import worst_route,oracle
from replay import placement
from itertools import product
from random import Random
from fractions import Fraction as F

def two_hop(x,v,body,cut,T,g,R,k):
    n=len(x)
    if x[-1]-x[0]<=R:return placement(x,v,body,cut,T,g,R,k)[0]
    for i in range(1,n-k-1):
        y,_=placement(x,v,body,cut,T,g,R,k,range(i,i+k+1))
        if y is not None:return y
    return None

def controls():
    x=(0,2,4,6,7,8,10,11);v=(0,0,1,0,1,1,1,0)
    R,k,cut,body,g=6,1,2,3,1
    assert placement(x,v,body,cut,0,g,R,k)[0] and worst_route(x,R,k)==3
    ext,_=placement(x,v,body,cut,1,g,R,k)
    assert worst_route(ext,R,k)==3
    assert two_hop(x,v,body,cut,F(999,1000),g,R,k) is None
    y=two_hop(x,v,body,cut,1,g,R,k)
    assert y and worst_route(y,R,k)==2
    print("ordinary robust radii pass at 0; robust 2-hop service requires 1 time unit")
    print("cut-directed extrema at 1 give",ext,"and require 3 hops")
    print("choice of verified lens block gives",y,"and serves in 2 hops")

def finite():
    rng=Random(241125)
    nchecks=0
    for trial in range(2000):
        n=rng.randrange(3,8);x=[0]
        for _ in range(n-1):x.append(x[-1]+rng.randrange(2,4))
        v=[0]+[rng.randrange(2) for _ in range(n-2)]+[0]
        cut=rng.randrange(1,n);body=F(x[cut-1]+x[cut],2)
        R,T,k,g=rng.randrange(1,x[-1]+1),rng.randrange(3),rng.randrange(min(n-1,3)),1
        want=two_hop(x,v,body,cut,T,g,R,k)
        _,B=placement(x,v,body,cut,T,g,R,k)
        # Difference-constraint system has integer input if obstacle is integer;
        # choose a doubled grid for the half-integer obstacle cases.
        brute=False
        for zz in product(*(range(int(2*a),int(2*b)+1) for a,b in B)):
            if any(z-a<2*g for a,z in zip(zz,zz[1:])):continue
            if oracle(zz,2*R,k)<=2:
                brute=True
                break
        assert (want is not None)==brute,(x,v,body,cut,T,R,k)
        assert want is None or worst_route(want,R,k)<=2
        nchecks+=1
    print(nchecks,"exact integer-grid robust-service comparisons")
if __name__=="__main__":controls();finite()
