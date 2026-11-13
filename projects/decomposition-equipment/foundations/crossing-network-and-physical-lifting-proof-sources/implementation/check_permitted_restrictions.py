from itertools import product
import json
# Exhaustively compare direct cartesian restrictions with graph;span;converse.
cases=0
for na,nb,nc,nd in product(range(1,3),repeat=4):
    A=range(na);B=range(nb);C=range(nc);D=range(nd)
    for f in product(B,repeat=na):
        for g in product(C,repeat=nd):
            # At most three genuinely distinct event records, repeated endpoints allowed.
            for nm in range(4):
                for ends in product(list(product(B,C)),repeat=nm):
                    direct={(a,m,d) for a in A for m in range(nm) for d in D
                            if f[a]==ends[m][0] and ends[m][1]==g[d]}
                    first={(a,m) for a in A for m in range(nm) if f[a]==ends[m][0]}
                    composite={(a,m,d) for a,m in first for d in D if ends[m][1]==g[d]}
                    assert direct==composite
                    assert all(ends[m]==(f[a],g[d]) for a,m,d in composite)
                    cases+=1
# Total deterministic circuits have one execution per input: converse possible iff bijection.
map_cases=0
for na,nb in product(range(1,5),repeat=2):
    for f in product(range(nb),repeat=na):
        converse_total_deterministic=all(sum(v==b for v in f)==1 for b in range(nb))
        bijective=len(set(f))==na==nb
        assert converse_total_deterministic==bijective
        map_cases+=1
print(json.dumps({'restriction_instances':cases,'total_deterministic_map_instances':map_cases,
 'all_checks_passed':True},indent=2))
