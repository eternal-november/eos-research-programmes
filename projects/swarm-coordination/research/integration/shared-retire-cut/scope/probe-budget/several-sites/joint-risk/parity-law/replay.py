#!/usr/bin/env python3
"""Independent exact decision search, keeping both parity-class scores."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb
from random import Random
import json


def pareto(m, budget):
    def clean(c):
        viz=set(c)
        return tuple(sorted(p for p in viz if not any(
            q!=p and q[0]>=p[0] and q[1]>=p[1] for q in viz)))
    @lru_cache(None)
    def dp(states,ready,remain):
        if not states or remain<0:
            return ((0,0),)
        if ready.bit_count()==m:
            e=sum(not (w.bit_count()%2) for w in states)
            return ((e,len(states)-e),)
        if remain< m-ready.bit_count():
            return ((0,0),)
        z=[]
        for i in range(m):
            if ready>>i&1:
                continue
            for b in (0,1):
                yes=tuple(w for w in states if (w>>i)&1==b)
                no=tuple(w for w in states if (w>>i)&1!=b)
                lhs=dp(yes,ready|1<<i,remain-1)
                rhs=dp(no,ready|1<<i,remain-2)
                z.extend((a+c,b+d) for (a,b) in lhs for (c,d) in rhs)
        return clean(z)
    return dp(tuple(range(1<<m)),0,budget)


def law_checks():
    rng=Random(523)
    checks=0
    for m in range(2,7):
        S=1<<m
        for _ in range(50):
            base=[rng.randrange(1,9) for _ in range(S)]
            even=[i for i in range(S) if not i.bit_count()%2]
            odd=[i for i in range(S) if i.bit_count()%2]
            e,o=min(base[i] for i in even),min(base[i] for i in odd)
            l=Q(rng.randrange(-2*e,2*o+1),2)
            u=Q(rng.randrange(int(2*l),2*o+1),2)
            sign=[1 if i in even else -1 for i in range(S)]
            variants=[[v+t*s for v,s in zip(base,sign)] for t in (l,u)]
            for first,second in zip(*variants):
                assert first>=0 and second>=0
            for k in range(m):
                for j in range(S):
                    if j>>k&1:
                        continue
                    assert base[j]+base[j|1<<k]==variants[0][j]+variants[0][j|1<<k]==variants[1][j]+variants[1][j|1<<k]
                    checks+=1
            assert min(max(x) for x in zip(*variants))==min(e+u,o-l)
            r=max(l,min(u,Q(o-e,2)))
            assert min(e+r,o-r)==min(e+u,o-l,Q(e+o,2))
    return checks


def replay():
    intervals=known=0
    for m in range(2,6):
        N=1<<(m-1)
        for d in range(1,m+1):
            S=pareto(m,2*m-d)
            A=sum(comb(m-1,j) for j in range(d-1))
            C=comb(m-1,d-1)
            vals=[Q(j,8) for j in range(9)]
            for p in vals:
                true=min(1-(p*e+(1-p)*o)/N for e,o in S)
                assert true==(A+C*min(p,1-p))/N
                known+=1
            for l,u in product(vals,repeat=2):
                if l>u:
                    continue
                true=min(max(1-(p*e+(1-p)*o)/N for p in (l,u)) for e,o in S)
                target=min(max((A+p*j+(1-p)*(C-j))/N for p in (l,u))
                           for j in range(C+1))
                assert true==target
                intervals+=1
    assert pareto(3,4)==((1,3),(2,2),(3,1))
    return dict(exact_known_law_comparisons=known,
                exact_interval_games=intervals,
                proper_marginal_invariances=law_checks(),
                three_resources_two_reads_short_known="1/4",
                three_resources_two_reads_short_robust_without_coin="1/2")


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
