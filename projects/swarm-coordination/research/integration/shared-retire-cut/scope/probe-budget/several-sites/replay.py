#!/usr/bin/env python3
"""Exact extremal trees and finite same-interface solver comparisons."""
from functools import lru_cache
from itertools import combinations, permutations
from math import comb
from random import Random
import json


def direct(W,k):
    n=max(w.bit_length() for w in W)
    @lru_cache(None)
    def step(active,tested,positive):
        if not active or positive==k:
            return 0
        ans=n+1
        for i in range(n):
            b=1<<i
            if tested&b or not any(w&b for w in active):
                continue
            yes=tuple(w for w in active if w&b)
            no=tuple(w for w in active if not w&b)
            ans=min(ans,1+max(step(yes,tested|b,positive+1),
                              step(no,tested|b,positive)))
        return ans
    return step(tuple(W),0,0)


def ordered_pair(W,n):
    E=[tuple(i for i in range(n) if w>>i&1) for w in W]
    best=n
    for perm in permutations(range(n)):
        pos={v:i+1 for i,v in enumerate(perm)}
        later={v:0 for v in perm}
        for i,j in E:
            first=i if pos[i]<pos[j] else j
            later[first]+=1
        best=min(best,max(pos[i]+d for i,d in later.items() if d))
    return best


def extremal(B,k):
    nodes={}
    W=[]
    def rec(prefix,ps,z,used):
        if ps==k:
            W.append(used)
            return
        index=len(nodes)
        nodes[prefix]=index
        rec(prefix+(1,),ps+1,z,used|1<<index)
        if z<B-k:
            rec(prefix+(0,),ps,z+1,used)
    rec((),0,0,0)
    return nodes,W


def play(G,W,k):
    used=()
    p=0
    while p<k:
        v=(W>>G[used])&1
        p+=v
        used+=(v,)
    return len(used)


def replay():
    constructions=replays=minimax=graph_checks=0
    for B in range(1,13):
        for k in range(1,B+1):
            tree,W=extremal(B,k)
            assert len(tree)==comb(B+1,k)-1
            assert len(W)==len(set(W))==comb(B,k)
            pop=0
            for w in W:
                assert w.bit_count()==k
                assert play(tree,w,k)<=B
                pop|=w
                replays+=1
            assert pop==(1<<len(tree))-1
            if len(tree)<=12:
                assert direct(W,k)==B
                minimax+=1
            constructions+=1
    rng=Random(521)
    for n in range(2,7):
        full=sorted((1<<i)+(1<<j) for i,j in combinations(range(n),2))
        tables=range(1,1<<len(full)) if n<5 else [rng.randrange(1,1<<len(full)) for _ in range(100)]
        for t in tables:
            W=[w for i,w in enumerate(full) if t>>i&1]
            assert direct(W,2)==ordered_pair(W,n)
            graph_checks+=1
    assert direct([5,9,10],2)==3
    return dict(extremal_families=constructions,extremal_world_replays=replays,
                extremal_minimax_checks=minimax,
                graph_order_equivalences=graph_checks,
                largest_extremal_site_count=comb(13,6)-1)


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
