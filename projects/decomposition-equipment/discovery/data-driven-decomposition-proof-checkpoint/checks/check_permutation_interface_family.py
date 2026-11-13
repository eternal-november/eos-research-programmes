from itertools import permutations, combinations
from math import factorial, comb
import json
checks={"query_identification":0,"static_profile_counts":0,"crossing_profile_counts":0,"swap_repairs":0,"message_distinctness":0}
for n in range(2,8):
    ps=list(permutations(range(n)))
    for k in range(1,n):
        scopes=[frozenset((i+j)%n for j in range(k)) for i in range(n)]
        sigs={tuple(tuple(sorted(p[i] for i in U)) for U in scopes) for p in ps}
        assert len(sigs)==factorial(n)
        checks['query_identification']+=len(ps)
        S=set(range(k))
        profiles={frozenset(p[i] for i in S) for p in ps}
        assert len(profiles)==comb(n,k)
        checks['static_profile_counts']+=1
        if n<=6:
            for p in ps:
                L=set(p[i] for i in S)
                for i in S:
                    for j in set(range(n))-S:
                        p2=list(p);p2[i],p2[j]=p2[j],p2[i]
                        assert set(p2[t] for t in S)==(L-{p[i]})|{p[j]}
                        checks['swap_repairs']+=1
            for L in profiles:
                outs={frozenset((set(L)-{a})|{b}) for a in L for b in set(range(n))-set(L)}
                assert len(outs)==k*(n-k)
                checks['message_distinctness']+=1
    if n<=6:
        S=set(range(n//2))
        for l in range(1,n):
            for tt in combinations(range(n),l):
                T=set(tt)
                cells=[S&T,S-T,T-S,set(range(n))-(S|T)]
                expected=factorial(n)
                for cell in cells: expected//=factorial(len(cell))
                profiles={(frozenset(p[i] for i in S),frozenset(p[i] for i in T)) for p in ps}
                assert len(profiles)==expected
                valid={(A,B) for A in map(frozenset,combinations(range(n),len(S))) for B in map(frozenset,combinations(range(n),len(T))) if len(A&B)==len(S&T)}
                assert profiles==valid
                for A,B in profiles:
                    witnesses=sum(frozenset(p[i] for i in S)==A and frozenset(p[i] for i in T)==B for p in ps)
                    expectedw=1
                    for cell in cells:expectedw*=factorial(len(cell))
                    assert witnesses==expectedw
                checks['crossing_profile_counts']+=1
print(json.dumps({'status':'PASS','checks':checks},indent=2))
