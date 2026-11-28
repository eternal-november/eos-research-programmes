#!/usr/bin/env python3
"""Check both recurrent FIFO quotients; the written proof covers arbitrary n."""
from itertools import combinations, permutations
from math import factorial
import json
import random

def drop(q, ids):
    return tuple(x for x in q if x not in ids)
def step(q, ids):
    tail=drop(q,ids)
    return (tail[0],tail[1:]) if tail else (None,())
def upper(full, small, m, k, reset):
    """Exhaust all legal removal choices at every grant on this named order."""
    roots=[(full,small,m,k)]
    visited=set()
    count=0
    while roots:
        q,p,left,budget=roots.pop()
        state=q,p,left,budget
        if state in visited or left==0 or not q:
            continue
        visited.add(state)
        for amt in range(min(budget,len(q))+1):
            for deleted in combinations(q,amt):
                a,r=step(q,deleted)
                b,s=step(p,deleted)
                assert a==b
                count+=1
                if a is not None:
                    roots.append((r,s,left-1,k if reset else budget-amt))
    return count

def lower(a,b,m,k,reset):
    j=next(i for i,(x,y) in enumerate(zip(a,b)) if x!=y)
    excess=max(0,j-m+1)
    assert excess<=(m*k if reset else k)
    total=0
    for t in range(m):
        # With fresh budgets take whole front chunks at each round.
        # With cumulative budget every required deletion fits in round one.
        take=min(excess,k) if reset else excess
        ids=a[:take]
        assert ids==b[:take]
        excess-=take
        total+=take
        x,a=step(a,ids)
        y,b=step(b,ids)
        if x!=y:
            assert excess==0
            return total,t+1
    raise AssertionError("no distinguishing grant")

def main():
    count=0
    for n in range(1,8):
        full=tuple(range(n))
        for m in range(1,n+2):
            for k in range(n+1):
                for reset in (False,True):
                    h=min(n,m*(k+1) if reset else k+m)
                    count+=upper(full,full[:h],m,k,reset)
    witness=0
    rng=random.Random(839)
    for n in range(2,7):
        full=tuple(range(n))
        orders=list(permutations(full))
        for m in range(1,n+1):
            for k in range(n+1):
                for reset in (False,True):
                    h=min(n,m*(k+1) if reset else k+m)
                    assert len(set(w[:h] for w in orders))==factorial(n)//factorial(n-h)
                    for a in orders:
                        b=orders[rng.randrange(len(orders))]
                        if a[:h]!=b[:h]:
                            lower(a,b,m,k,reset)
                            witness+=1
    a=(2,3,4,5,6,7)
    b=(2,3,4,6,5,7)
    assert a[:3]==b[:3] and lower(a,b,2,1,True)==(2,2)
    print(json.dumps(dict(adaptive_checks=count,distinguishing_witnesses=witness,
                          six_one_grant=120,six_two_grants=360),sort_keys=True))
if __name__=="__main__":
    main()
