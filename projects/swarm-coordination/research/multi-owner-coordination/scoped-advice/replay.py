from itertools import combinations
from math import comb

def masks(n,k):
    return [sum(1<<i for i in s) for s in combinations(range(n),k)]

def feasible_subset_size_range(n,k,m):
    return range(max(0,k-(n-m)),min(k,m)+1)

policy_checks=0; additions=0
for n in range(1,9):
    universe=(1<<n)-1
    for k in range(n+1):
        full=masks(n,k)
        for scope in range(1<<n):
            by={}
            for s in full:by.setdefault(s&scope,[]).append(s)
            m=scope.bit_count()
            assert len(by)==sum(comb(m,t) for t in feasible_subset_size_range(n,k,m))
            for p,S in by.items():
                miss=k-p.bit_count()
                for b in (1<<i for i in range(n)):
                    v={bool(s&b) for s in S}
                    if scope&b:
                        assert v=={bool(p&b)}
                        policy_checks+=1
                    else:
                        assert v==({False} if miss==0 else
                                    {True} if miss==n-m else {False,True})
                        additions+=1
print(policy_checks,"existing-scope exact queries and",additions,
      "scope expansions matched distinct history enumeration")
print("masked histories", [{0,2},{0,3}], "older scope", {0,1},
      "same authorized report", {0}, "future query", 2, "has no uniform answer")
