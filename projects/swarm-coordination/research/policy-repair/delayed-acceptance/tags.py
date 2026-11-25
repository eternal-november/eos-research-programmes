"""Stamp compression where label is chosen at acceptance, without delay."""
from itertools import product, combinations
from solve import compile_rule,play

def rows(label,a,b,D):
    return [(c+a,c+b,c+d,y) for c,y in enumerate(label) for d in range(D+1)]

def compatible(label,a,b,D):
    w=b-a
    return all(label[i]!=label[j] for i,j in combinations(range(len(label)),2)
                 if w<j-i<=D)

def consistency():
    n=0
    for H in range(1,6):
        for D in range(5):
            for a,b in [(0,0),(1,1),(1,2),(1,3),(2,3),(2,4)]:
                if D>b:continue # individual waiting feasibility
                for label in product(range(3),repeat=H+1):
                    data=rows(label,a,b,D)
                    if compile_rule(data) is not False:
                        play(data,compile_rule(data))
                    # Always wait. Each co-arrival group must be feasible.
                    groups={}
                    for lo,hi,r,y in data:
                        L,U=groups.get((r,y),(r,hi))
                        groups[(r,y)]=(max(L,lo),min(U,hi))
                    assert compatible(label,a,b,D)==all(L<=U for L,U in groups.values())
                    n+=1
    return n

if __name__=="__main__":
    print("tag/arrival graph comparisons",consistency())
    a,b,D,H=2,3,3,4
    bad=[tag for tag in product(range(2),repeat=H+1) if compile_rule(rows(tag,a,b,D))]
    assert not bad, bad
    good=next(tag for tag in product(range(3),repeat=H+1) if compile_rule(rows(tag,a,b,D)))
    assert compatible(good,a,b,D)
    routes=rows(good,a,b,D)
    assert compile_rule(routes)[0] is None
    play(routes,compile_rule(routes))
    print("need 3 fixed tag values, with or without default",good)
    max_cohort=max(sum(1 for c in range(H+1) if c<=r<=c+D) for r in range(H+D+1))
    assert max_cohort==4
    print("every reachable fixed-arrival cohort of at most 4 consecutive ticks needs at most 2 tags")
