from fractions import Fraction as F
from math import ceil
from random import Random
rng=Random(81)
for test in range(500):
    p=[F(rng.randrange(0,50),rng.randrange(1,10)) for _ in range(rng.randrange(1,8))]
    def split(extra):
        result=[]
        for x,v in enumerate(p):
            n=max(1,ceil(v))+extra
            result += [(x,v/n)]*n
        return result
    s=split(0); z=split(rng.randrange(0,4))
    rel={(i,j):(v*w/p[x] if p[x] else F(0)) for i,(x,v) in enumerate(s) for j,(y,w) in enumerate(s) if x==y}
    assert all(0<=v<=1 for v in rel.values())
    for i,(_,v) in enumerate(s):
        assert sum(w for (a,b),w in rel.items() if a==i)==v
        assert sum(w for (a,b),w in rel.items() if b==i)==v
    r={(j,i):(v*w/p[x] if p[x] else F(0)) for j,(x,v) in enumerate(z) for i,(y,w) in enumerate(s) if x==y}
    assert all(0<=v<=1 for v in r.values())
    for j,(_,v) in enumerate(z): assert sum(w for (a,b),w in r.items() if a==j)==v
    for i,(_,v) in enumerate(s): assert sum(w for (a,b),w in r.items() if b==i)==v
    # Event restriction is saturated along the raw refinement.
    event={x for x in range(len(p)) if rng.randrange(2)}
    for x in event: assert sum(v for y,v in s if y==x)==p[x]
print('PASS: 500 exact-rational splitting, relation, refined-lift and saturated-restriction tests.')
print('Finite diagnostics only; no verification of arbitrary coefficient arrows or general coherence.')
