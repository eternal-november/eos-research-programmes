"""Exact rational checks of the crossing product stability lemma.
Finite checks corroborate, and do not replace, the proof in Discovery_and_Reuse.md.
"""
from fractions import Fraction as F
from itertools import combinations, product
import random,json

def parts(xs):
    if not xs: yield (); return
    a,*tail=xs
    for p in parts(tail):
        yield ((a,),)+p
        for j in range(len(p)):
            yield p[:j]+(tuple(sorted((a,)+p[j])),)+p[j+1:]

def tv(p,q): return sum(abs(p[k]-q[k]) for k in p)/2

def marginal(p,S):
    out={x:F(0) for x in product((0,1),repeat=len(S))}
    for x,w in p.items():out[tuple(x[i] for i in S)]+=w
    return out

def random_product(pi,n,rng):
    laws=[]
    for B in pi:
        weights=[rng.randrange(1,10) for _ in range(2**len(B))];z=sum(weights)
        laws.append(dict(zip(product((0,1),repeat=len(B)),(F(w,z) for w in weights))))
    out={}
    for x in product((0,1),repeat=n):
        out[x]=F(1)
        for B,law in zip(pi,laws):out[x]*=law[tuple(x[i] for i in B)]
    return out

rng=random.Random(202610291755);n=4;count=0;maxratio=F(0)
partitions=[p for p in parts(list(range(n))) if max(map(len,p))<=2]
for pi,tau in product(partitions,repeat=2):
    meet=[tuple(sorted(set(B)&set(C))) for B in pi for C in tau if set(B)&set(C)]
    for _ in range(3):
        P=random_product(pi,n,rng);Q=random_product(tau,n,rng)
        d=max(tv(marginal(P,S),marginal(Q,S)) for k in (1,2) for S in combinations(range(n),k))
        dist=tv(P,Q);coeff=len(pi)+len(tau)+len(meet)
        assert dist<=coeff*d
        assert coeff<=3*n
        if d:maxratio=max(maxratio,dist/d)
        count+=1
# The block-size universe cannot be deleted: all proper marginals can agree.
U={x:F(1,16) for x in product((0,1),repeat=n)}
P={x:F(1,8) if sum(x)%2==0 else F(0) for x in U}
Q={x:F(1,8) if sum(x)%2==1 else F(0) for x in U}
assert tv(P,Q)==1
assert all(marginal(P,S)==marginal(Q,S) for k in range(1,n) for S in combinations(range(n),k))
print(json.dumps({'status':'PASS','exact_crossing_cases':count,
 'maximum_observed_TV_to_local_error_ratio':str(maxratio),
 'outside_block_bound_equal_proper_marginals_global_TV':1},indent=2))
