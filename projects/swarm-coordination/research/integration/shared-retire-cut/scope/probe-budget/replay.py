#!/usr/bin/env python3
"""Compare minimum covering sets with a direct adaptive inspection game."""
from functools import lru_cache
from itertools import product
import json
import random

INF=10**9


def optimal(worlds,offered,costs,infer):
    best=INF
    K=offered
    while K:
        if all(K&w for w in worlds):
            weights=[c for i,c in enumerate(costs) if K>>i&1]
            best=min(best,sum(weights)-(max(weights) if infer else 0))
        K=offered&(K-1)
    return best


def game(worlds,offered,costs,infer):
    @lru_cache(None)
    def step(active,unknown,known):
        if not active or known:
            return 0
        if infer and any(unknown>>i&1 and all(w>>i&1 for w in active)
                         for i in range(len(costs))):
            return 0
        val=INF
        for i,c in enumerate(costs):
            bit=1<<i
            if not unknown&bit:
                continue
            yes=tuple(w for w in active if w&bit)
            no=tuple(w for w in active if not w&bit)
            val=min(val,c+max(step(yes,unknown^bit,True),
                              step(no,unknown^bit,False)))
        return val
    return step(tuple(worlds),offered,False)


def minimize(ws):
    return tuple(w for w in ws if not any(u!=w and w&u==u for u in ws))


def noisy_cover(W,Q,c,b,infer):
    best=INF
    for mult in product(*(range(b+2) if Q>>i&1 else (0,) for i in range(len(c)))):
        possible=[w for w in W if sum(m for i,m in enumerate(mult) if w>>i&1)<=b]
        has_terminal=infer and any(Q>>i&1 and all(w>>i&1 for w in possible)
                                   for i in range(len(c)))
        if not possible or has_terminal:
            best=min(best,sum(x*y for x,y in zip(mult,c)))
    return best


def noisy_game(W,Q,c,b,infer):
    @lru_cache(None)
    def step(paths):
        if not paths:
            return 0
        if infer and any(Q>>i&1 and all(w>>i&1 for w,_ in paths)
                         for i in range(len(c))):
            return 0
        ans=INF
        for i,price in enumerate(c):
            if not Q>>i&1:
                continue
            fail=tuple((w,credit-int(bool(w>>i&1))) for w,credit in paths
                       if credit>0 or not w>>i&1)
            if fail==paths:
                continue
            yes=0 # a checked free site can be used immediately
            ans=min(ans,price+max(yes,step(fail)))
        return ans
    return step(tuple((w,b) for w in W))


def replay():
    checks=impossible=0
    r=random.Random(482)
    for n in range(1,4):
        N=1<<n
        for table in range(1,1<<N):
            W=tuple(i for i in range(N) if table>>i&1)
            Z=minimize(W)
            c=tuple(r.randrange(6) for i in range(n))
            rejected=[]
            for Q in range(N):
                if not all(Q&w for w in W):
                    rejected.append(Q)
                for inference in (False,True):
                    exp=game(W,Q,c,inference)
                    assert exp==optimal(W,Q,c,inference)==optimal(Z,Q,c,inference)
                    checks+=1
                    impossible+=exp==INF
            maxima=[q for q in rejected
                    if not any(q!=z and q&z==q for z in rejected)]
            assert sorted((N-1)^q for q in maxima)==list(Z)
    for _ in range(600):
        n=r.randrange(4,8)
        N=1<<n
        W=tuple(sorted(set(r.randrange(N) for _ in range(r.randrange(1,20)))))
        c=tuple(r.randrange(1,12) for _ in range(n))
        Q=r.randrange(N)
        for f in (False,True):
            exp=game(W,Q,c,f)
            assert exp==optimal(W,Q,c,f)
            checks+=1
            impossible+=exp==INF
    for n in range(3,10):
        N=1<<n
        singleton=tuple(1<<i for i in range(n))+(N-1,)
        one_busy=tuple((N-1)^(1<<i) for i in range(n))
        assert optimal(singleton,N-1,[1]*n,True)==n-1
        assert optimal(one_busy,N-1,[1]*n,True)==1
    faults=0
    for _ in range(420):
        n=r.randrange(1,5)
        W=tuple(sorted(set(r.randrange(1<<n) for _ in range(r.randrange(1,10)))))
        c=[r.randrange(5) for i in range(n)]
        Q=r.randrange(1<<n)
        for b in range(4):
            for inference in (False,True):
                z=noisy_game(W,Q,c,b,inference)
                assert z==noisy_cover(W,Q,c,b,inference)
                assert z==noisy_cover(minimize(W),Q,c,b,inference)
                if not b:
                    assert z==optimal(W,Q,c,inference)
                faults+=1
    return dict(adaptive_tree_comparisons=checks,
                false_negative_game_comparisons=faults, infeasible_offers=impossible,
                equal_marginal_families=7)


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
