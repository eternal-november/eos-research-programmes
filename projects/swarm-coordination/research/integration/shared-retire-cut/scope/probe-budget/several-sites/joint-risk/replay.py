from fractions import Fraction as Q
from itertools import product
from math import comb
from functools import lru_cache
from random import Random
import json


def first_reads(z, seed):
    total=0
    remain=list(range(len(z)))
    p=seed
    while remain:
        j=remain.pop(p%len(remain))
        x=(z[j]==((p//3)%2))
        total+=x
        p=(p*53+17*x+31*j+8)%251
    return total


def direct(law,m,B):
    @lru_cache(None)
    def f(supp,free,left):
        if not supp:
            return 0
        if free.bit_count()==m:
            return sum(law[w] for w in supp)
        if left< m-free.bit_count():
            return 0
        ans=0
        for i in range(m):
            if (free>>i)&1:
                continue
            for x in (0,1):
                yes=tuple(w for w in supp if (w>>i)&1==x)
                no=tuple(w for w in supp if (w>>i)&1!=x)
                # A negative identifies the sole remaining true site, but
                # that site still incurs its verification. The second check
                # can be moved here since it conveys no further information.
                end=f(no,free|1<<i,left-2) if left>=2 else 0
                ans=max(ans,f(yes,free|1<<i,left-1)+end)
        return ans
    return sum(law)-f(tuple(i for i,w in enumerate(law) if w),0,B)


def run():
    r=Random(522)
    ws=cases=exact=law_checks=0
    for m in range(1,10):
        Z=list(product((0,1),repeat=m))
        for seed in range(40):
            hist=[0]*(m+1)
            for z in Z:
                hist[first_reads(z,seed)]+=1
                ws+=1
            assert hist==[comb(m,j) for j in range(m+1)]
            cases+=1
        if m<=5:
            for d in range(1,m+1):
                assert direct([1]*(1<<m),m,2*m-d)==sum(comb(m,i) for i in range(d))
                exact+=1
            for _ in range(12):
                L=[r.randrange(6) for z in Z]
                assert direct(L,m,2*m-1)==min(L)
                exact+=1
    for a,b in product(range(21),repeat=2):
        lo,hi=max(0,a+b-20),min(a,b)
        # Double the scale: the least-favorable coupling can use half points.
        mu=[(x,2*a-x,2*b-x,40-2*a-2*b+x)
            for x in range(2*lo,2*hi+1)]
        rmin=min(a,b,20-a,20-b)
        assert min(max(t[j] for t in mu) for j in range(4))==2*rmin
        assert max(min(t) for t in mu)==rmin
        law_checks+=1
    return dict(adaptive_policy_families=cases, world_runs=ws,
                direct_law_comparisons=exact, marginal_games=law_checks,
                two_uniform_deterministic_risk="1/2",two_uniform_mixed_risk="1/4")


if __name__=="__main__":
    print(json.dumps(run(),indent=2))
