#!/usr/bin/env python3
"""Finite exact comparison of total and separately attributed world intents."""
import itertools as it
import json
from random import Random
X=(1,0,0); Z=(0,0,1)

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def apply(r,v):return tuple(sum(a*b for a,b in zip(row,v)) for row in r)
def inverse(r):return tuple(zip(*r))
def rotation_family():
    for p in it.permutations(range(3)):
        inv=sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
        for signs in it.product([-1,1],repeat=3):
            if signs[0]*signs[1]*signs[2] != (-1)**inv:continue
            yield tuple(tuple(signs[i] if j==p[i] else 0 for j in range(3)) for i in range(3))
R=tuple(rotation_family())
assert len(R)==24

def quotient(modes,demands,separate):
    return {tuple(tuple(apply(inverse(r),v) for v in ((a,b) if separate else (add(a,b),)))
                  for a,b in demands) for r in modes}

def oracle(modes,demands,separate):
    # Direct solution search of local vector components, not inversion.
    def options(r,targets):
        return tuple(frozenset(z for z in it.product(range(-2,3),repeat=3)
                             if apply(r,z)==target) for target in targets)
    for h,v in demands:
        target=(h,v) if separate else (add(h,v),)
        by_mode=[options(r,target) for r in modes]
        if not all(set.intersection(*(set(row[i]) for row in by_mode)) for i in range(len(target))):
            return False
    return True

def demo():
    identity=((1,0,0),(0,1,0),(0,0,1))
    swap=((0,0,1),(0,-1,0),(1,0,0))
    assert identity in R and swap in R
    assert apply(swap,add(X,Z))==add(X,Z)
    assert apply(swap,X)==Z and apply(swap,Z)==X
    assert oracle([identity,swap],[(X,Z)],False)
    assert not oracle([identity,swap],[(X,Z)],True)
    assert len(quotient(R,[(X,Z)],False))==12
    assert len(quotient(R,[(X,Z)],True))==24
    rnd=Random(549)
    checked=0
    for _ in range(700):
        modes=rnd.sample(R,rnd.randrange(1,8))
        ds=[((rnd.randrange(-1,2),rnd.randrange(-1,2),0),(0,0,rnd.randrange(-1,2)))
            for _ in range(rnd.randrange(1,5))]
        for sep in (False,True):
            assert (len(quotient(modes,ds,sep))==1)==oracle(modes,ds,sep)
            checked+=1
    return dict(total_only_classes=12,separately_attributed_classes=24,
        exact_reference_cases=checked,same_total_different_authorized_decomposition=True)

if __name__=='__main__':print(json.dumps(demo(),sort_keys=True,indent=2))
