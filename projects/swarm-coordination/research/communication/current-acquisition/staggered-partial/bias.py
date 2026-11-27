"""Exact balanced lower-obstruction term with a bounded moving common bias."""
from fractions import Fraction as F
from itertools import product
from random import Random

def unconstrained(xs,g,D):
    """If balance holds, the result and a sufficient amplitude of a maximizing path."""
    assert len(xs)==len(g) and len(xs)>0 and sum(g)==0
    p=F(0); a=F(0); lo=F(0); hi=F(0); total=F(0)
    # g·b = -Σ prefix_g (b_next-b_current).
    for i,(t,u) in enumerate(zip(xs,xs[1:])):
        p+=g[i]
        w=D*(u-t)
        assert w>=0
        if p:
            a+=-w if p>0 else w
            total+=abs(p)*w
            lo=min(lo,a)
            hi=max(hi,a)
        # Zero weights can bridge active runs. This particular witness
        # leaves them constant; the span here is sufficient, not minimal.
    return total,(hi-lo)/2

def minimum_amplitude(xs,g,D):
    assert len(xs)==len(g)>0 and sum(g)==0
    up=down=worst=prefix=F(0)
    for i,(t,u) in enumerate(zip(xs,xs[1:])):
        prefix+=g[i]
        d=D*(u-t)
        assert d>=0
        l,h=(-d,-d) if prefix>0 else (d,d) if prefix<0 else (-d,d)
        up=max(0,up+l)
        down=max(0,down-h)
        worst=max(worst,up,down)
    return worst/2

def independent_pair(B,D,dt):
    # Exact vertices of the feasible difference strip, not use min formula.
    p=[]
    # Enumerate x,y between +/- B with |y-x| <= D*dt.
    c=D*dt
    for x in (-B,B):
        for y in (-B,B,x-c,x+c):
            if abs(y)<=B and abs(x-y)<=c:
                p.extend([(x,y),(y,x)])
    return max(x-y for x,y in p)

def audit():
    r=Random(20261127)
    for _ in range(2048):
        B,D,dt=(F(r.randrange(31),r.randrange(1,10)) for _ in range(3))
        assert independent_pair(B,D,dt)==min(2*B,D*dt)
    return 2048
if __name__=='__main__':print(audit())
