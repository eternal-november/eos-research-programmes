#!/usr/bin/env python3
"""Exact tiny-instance audit of three-stream hardness and a matching exception."""
from itertools import combinations, product
import json
import random


def matching(g):
    by_phase={}
    def add(i,seen):
        for phase in g[i]:
            if phase in seen:
                continue
            seen.add(phase)
            if phase not in by_phase or add(by_phase[phase],seen):
                by_phase[phase]=i
                return True
        return False
    for i in range(len(g)):
        add(i,set())
    return by_phase


def feasible(model,n):
    g,f=model
    return len(matching(g))==n


def masks(model,n):
    g,f=model
    result=[]
    for p in combinations(range(n),sum(f)):
        S=set(p)
        restricted=[allowed&S if fail else allowed-S for allowed,fail in zip(g,f,strict=True)]
        if len(matching(restricted))==n:
            result.append(S)
    return result


def reductions(edges,q):
    n=len(edges)
    indices=set(range(n))
    parts=[tuple({i for i,e in enumerate(edges) if e[k]==j}
                 for j in range(q)) for k in range(3)]
    X,Y,Z=parts
    if any(not s for component in parts for s in component):
        return None
    by_edges=list(X)+[s for group in Y for s in [group]*(len(group)-1)]
    b=(by_edges,[True]*q+[False]*(n-q))
    c_min=(list(Z)+[indices]*(n-q),[True]*q+[False]*(n-q))
    c_max=(list(Z)+[indices]*(n-q),[False]*q+[True]*(n-q))
    if not feasible(b,n):
        # In the proof, return an individually feasible NO instance instead.
        return None
    assert feasible(c_min,n) and feasible(c_max,n)
    return b,c_min,c_max


def direct_3dm(edges,q):
    return any(all(len({e[k] for e in es})==q for k in range(3))
               for es in combinations(edges,q))


def max_open_successes(models,a):
    pool=[]
    for g,f in models:
        for edges,fail in zip(g,f,strict=True):
            if fail:
                pool.append(edges-a)
    return len(a)+len(matching(pool))


def main():
    universe=list(product(range(2),repeat=3))
    domains=cert_yes=0
    for mask in range(1<<len(universe)):
        e=[u for i,u in enumerate(universe) if mask>>i&1]
        yes=direct_3dm(e,2)
        v=reductions(e,2)
        if v is None:
            assert not yes
            continue
        n=len(e)
        b,c_min,c_max=v
        left,right_min,right_max=(masks(s,n) for s in v)
        assert (min(len(x|y) for x,y in product(left,right_min))==2)==yes
        assert (max(len(x|y) for x,y in product(left,right_max))==n)==yes
        domains+=1
        cert_yes+=yes
    parity=[e for e in universe if sum(e)%2==0]
    n=len(parity)
    b,c,d=reductions(parity,2)
    assert min(len(x|y) for x,y in product(masks(b,n),masks(c,n)))==3
    assert max(len(x|y) for x,y in product(masks(b,n),masks(d,n)))==3
    rnd=random.Random(493)
    tested=0
    while tested<380:
        n=rnd.randrange(1,7)
        phases=set(range(n))
        a={i for i in phases if rnd.randrange(3)==0}
        models=[]
        for _ in range(rnd.randrange(1,5)):
            f=[bool(rnd.randrange(2)) for _ in range(n)]
            g=[{i for i in phases if rnd.randrange(3)!=0} if fail else phases for fail in f]
            models.append((g,f))
        if not all(feasible(s,n) for s in models):
            continue
        actual=max(len(a.union(*pieces)) for pieces in product(*(masks(s,n) for s in models)))
        assert max_open_successes(models,a)==actual
        tested+=1
    print(json.dumps(dict(hypergraphs=256,individually_matchable_reductions=domains,
        perfect_3D=cert_yes,unrestricted_successes_comparisons=tested,
        parity_triplets=parity,parity_min_count=3,parity_max_count=3),indent=2))


if __name__=='__main__':
    main()
