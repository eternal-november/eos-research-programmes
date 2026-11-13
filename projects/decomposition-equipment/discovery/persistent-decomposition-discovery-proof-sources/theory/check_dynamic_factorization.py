"""Finite regression checks for Exact_Dynamic_Factorization.md.
Pure Python, deterministic, no proof-assistant claim.
"""
from itertools import product
from math import gcd
from functools import reduce
import json, random
from pathlib import Path


def rank_one(M):
    r,c=len(M),len(M[0]) if M else 0
    return all(M[a][x]*M[b][y]==M[a][y]*M[b][x]
               for a in range(r) for b in range(a+1,r)
               for x in range(c) for y in range(x+1,c))


def factor_options(M):
    r,c=len(M),len(M[0])
    if not any(map(any,M)):
        raise ValueError('Zero matrix has potentially unbounded invisible factors')
    if not rank_one(M): return []
    j=next(j for j in range(c) if any(M[i][j] for i in range(r)))
    col=[M[i][j] for i in range(r)]
    h=reduce(gcd,col)
    p=tuple(v//h for v in col)
    k=next(i for i in range(r) if p[i])
    v=[]
    for j in range(c):
        assert M[k][j]%p[k]==0
        v.append(M[k][j]//p[k])
    assert all(M[i][j]==p[i]*v[j] for i in range(r) for j in range(c))
    g=reduce(gcd,v)
    q=tuple(x//g for x in v)
    return [(tuple(k*x for x in p),tuple((g//k)*x for x in q))
            for k in range(1,g+1) if g%k==0]

matrices=0
rank1=0
factors=0
for vals in product(range(4),repeat=4):
    M=[vals[:2],vals[2:]]
    if not any(vals): continue
    claimed=set(factor_options(M))
    actual=set()
    for d in product(range(4),repeat=2):
        for c in product(range(4),repeat=2):
            if all(d[i]*c[j]==M[i][j] for i in range(2) for j in range(2)):
                actual.add((d,c))
    assert claimed==actual,(M,claimed,actual)
    matrices+=1
    rank1+=bool(claimed)
    factors+=len(claimed)

# Actual graph edges carry distinct ids, endpoints and a shared interface event.
def paths(states,edges,n):
    if n==0:return [(s,(),s) for s in states]
    previous=paths(states,edges,n-1)
    return [(s,es+(i,),t) for s,es,u in previous
            for i,(v,t,j) in enumerate(edges) if u==v]

rng=random.Random(20261026)
path_cases=0
path_records=0
for trial in range(24):
    # Include repeats as literal distinct transition records.
    D=[(rng.randrange(2),rng.randrange(2),rng.randrange(2)) for _ in range(4)]
    F=[(rng.randrange(2),rng.randrange(2),rng.randrange(2)) for _ in range(4)]
    pairs=[(i,j) for i,d in enumerate(D) for j,f in enumerate(F) if d[2]==f[2]]
    E=[((D[i][0],F[j][0]),(D[i][1],F[j][1]),D[i][2]) for i,j in pairs]
    pair_id={pair:k for k,pair in enumerate(pairs)}
    for n in range(5):
        pE=paths(list(product(range(2),repeat=2)),E,n)
        pD=paths(range(2),D,n);pF=paths(range(2),F,n)
        constructed=set()
        for sd,ed,td in pD:
            for sf,ef,tf in pF:
                if tuple(D[i][2] for i in ed)==tuple(F[j][2] for j in ef):
                    constructed.add(((sd,sf),tuple(pair_id[p] for p in zip(ed,ef)),(td,tf)))
        assert set(pE)==constructed,(trial,n)
        assert len(pE)==len(set(pE))
        path_cases+=1;path_records+=len(pE)

# Count-level refactorization can erase synchronization provenance.
D=[0,1];F=[0,1]
old={(d,f) for d in D for f in F if d==f}
forgotten=set(product(D,F))
assert len(old)==2 and len(forgotten)==4
assert factor_options([[2]])==[((1,),(2,)),((2,),(1,))]

# Coarse exact dynamic factor, non-independent finer reset.
fine=[[int(ap==bp) for b,bp in product(range(2),repeat=2)]
      for a,ap in product(range(2),repeat=2)]
assert not rank_one(fine)
# Partial views retaining one reset marginal have uniform sums.
assert all(sum(row)==2 for row in fine)
assert all(sum(fine[i][j] for i in range(4))==2 for j in range(4))

result={
 'status':'PASS',
 'nonzero_2x2_integer_matrices_checked':matrices,
 'rank_one_matrices':rank1,
 'integral_outer_factor_options_checked':factors,
 'actual_graph_path_cases_lengths_0_through_4':path_cases,
 'actual_whole_path_records_compared':path_records,
 'synchronization_provenance_failure_detected':True,
 'coarse_success_fine_reset_failure_detected':True,
 'scope':'bounded exhaustive matrix cases and deterministic randomized finite graph fixtures; not a proof of the theorems'
}
out=Path(__file__).with_name('check_dynamic_factorization_results.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
