"""Rational/strict clock inequalities, with finite exact witness extraction."""
from fractions import Fraction as F
from itertools import product
from math import lcm
from random import Random
from cut import vertex_witness

def satisfiable(n,A):
    # Each edge carries (rational difference bound, strictness). A common
    # denominator D makes positive simple-cycle slack at least 1/D. A
    # strict edge can therefore be lowered by 1/(D*(n+1)) exactly.
    d=lcm(*(F(b).denominator for u,v,b,s in A),1)*(n+1)
    ini=[(u,v,int(F(b)*d)-int(s)) for u,v,b,s in A]
    t=vertex_witness(n,ini)
    if t is None:return None
    z=tuple(F(x,d) for x in t)
    assert accepts(A,z)
    return z

def accepts(A,z):
    return all((z[v]-z[u]<b if s else z[v]-z[u]<=b) for u,v,b,s in A)

def bad(n,A,rs):
    assert satisfiable(n,A) is not None
    for selected in product(*rs):
        xy=tuple((v,u,-b,not a) for u,v,b,a in selected)
        z=satisfiable(n,tuple(A)+xy)
        if z is not None:
            assert not any(accepts(q,z) for q in rs)
            return z
    return None

if __name__=='__main__':
    # 0 < T[1]-T[0] < 1: rounding to integer ticks is incomplete.
    assert satisfiable(2,((0,1,1,True),(1,0,0,True))) is not None
    # Zero-sum strict cycle is impossible even though non-strict passes.
    assert satisfiable(2,((0,1,1,True),(1,0,-1,False))) is None
    assert satisfiable(2,((0,1,1,False),(1,0,-1,False)))==(F(0),F(1))
    domain=((0,1,1,False),(1,0,1,False))
    a=((0,1,0,True),) # offset < 0
    b=((1,0,0,False),) # offset >= 0
    assert bad(2,domain,(a,b)) is None
    assert bad(2,domain,(a,((1,0,0,True),)))==(F(0),F(0))
    rng=Random(463);nchecks=0
    # Paired with exhaustive grid at mesh 1/(D(n+1)); anchoring implies
    # every returned canonical time is inside the enumerated interval.
    for _ in range(400):
        A=((0,1,1,False),(1,0,1,False),(0,2,1,False),(2,0,1,False))
        X=tuple((*rng.sample(range(3),2),F(rng.randrange(-2,3),2),bool(rng.randrange(2))) for i in range(rng.randrange(1,7)))
        w=satisfiable(3, A+X)
        # D*(n+1) = 4 or 8. Common mesh 1/8 admits every witness.
        values=[F(i,8) for i in range(-8,9)]
        assert (w is not None)==any(accepts(A+X,(0,*t)) for t in product(values,repeat=2))
        nchecks+=1
    print(nchecks,'rational systems match an independently exhaustive exact grid')
    print('strict zero cycle and same-time equality are distinguished without tick rounding')
