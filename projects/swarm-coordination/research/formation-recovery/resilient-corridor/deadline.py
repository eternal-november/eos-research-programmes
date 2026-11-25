"""Worst-case greedy radio hops after a bounded set of silent radios."""
from functools import cache
from itertools import combinations,product
from math import inf
from random import Random

def oracle(x,R,b):
    n=len(x);worst=0
    for k in range(min(b,n-2)+1):
        for drop in combinations(range(1,n-1),k):
            O=set(range(n))-set(drop)
            # Independent BFS, arbitrary neighbor direction allowed.
            Q=[0];D={0:0}
            for i in Q:
                for j in sorted(O-D.keys()):
                    if abs(x[i]-x[j])<=R:Q.append(j);D[j]=D[i]+1
            worst=max(worst,D.get(n-1,inf))
    return worst

def worst_route(x,R,b):
    n=len(x)
    last=tuple(max(j for j in range(i,n) if x[j]-x[i]<=R) for i in range(n))
    @cache
    def solve(i,e,budget):
        # i survived, (i,e] are already silent. Earlier radios no longer
        # enter forward greedy choices; nobody to the right of e is fixed.
        if last[i]==n-1:return 1 # intact end anchor
        fresh=last[i]-e
        assert fresh>=0
        if fresh<=budget:return inf # erase every remaining forward neighbor
        return 1+max(solve(j,last[i],budget-(last[i]-j))
                       for j in range(last[i]-budget,last[i]+1))
    return solve(0,0,b)

def run():
    n=0
    for count in range(2,8):
        for gaps in product(range(1,4),repeat=count-1):
            x=[0]
            for g in gaps:x.append(x[-1]+g)
            x=tuple(x)
            for R,b in product(range(1,6),range(min(count-1,4))):
                assert worst_route(x,R,b)==oracle(x,R,b),(x,R,b)
                n+=1
    print(n,"exact deletion/BFS versus frontier DP comparisons")
    x=(0,2,4,6,8)
    assert worst_route(x,4,0)==2 and worst_route(x,4,1)==3
    print("same robust connectivity, nominal 2 hop deadline fails after central radio loss; worst deadline 3")
if __name__=="__main__":run()
