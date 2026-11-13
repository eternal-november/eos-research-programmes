"""Finite regressions, Python stdlib only. Run python3 check_resource_paths.py."""
from itertools import combinations, product
import random, json

def dominates(p,q): return p[0] & q[0] == p[0] and p[1] <= q[1]
def prune(P):
    P=set(P)
    return frozenset(p for p in P if not any(q!=p and dominates(q,p) for q in P))
def compose(P,Q):
    return frozenset((s|t,c+d) for s,c in P for t,d in Q if not s&t)
def accept(P,K,B): return any(s&K==s and c<=B for s,c in P)
def powerset(xs):
    return [frozenset(c) for n in range(len(xs)+1) for c in combinations(xs,n)]

# Every finite family over a one-resource, three-cost universe.
universe=list(product(range(2),range(3)))
families=powerset(universe)
obs=lambda P:tuple(accept(P,K,B) for K in range(2) for B in range(3))
for P,Q in product(families,repeat=2):
    assert (obs(P)==obs(Q)) == (prune(P)==prune(Q))
    assert prune(P|Q)==prune(prune(P)|prune(Q))
    assert prune(compose(P,Q))==prune(compose(prune(P),prune(Q)))
# All triples of a smaller family, including empty witnesses/identities.
small=powerset(list(product(range(2),range(2))))
for P,Q,T in product(small,repeat=3):
    assert compose(compose(P,Q),T)==compose(P,compose(Q,T))
    assert prune(compose(prune(compose(P,Q)),T))==prune(compose(P,prune(compose(Q,T))))
for P in families:
    assert compose(P,{(0,0)})==P==compose({(0,0)},P)
# Larger resources: reproducible samples of independent endpoints' fibres.
rng=random.Random(20261113)
for _ in range(3000):
    P,Q,T=[frozenset((rng.randrange(16),rng.randrange(7)) for _ in range(rng.randrange(12))) for _ in range(3)]
    assert prune(compose(P,Q))==prune(compose(prune(P),prune(Q)))
    assert prune(compose(compose(P,Q),T))==prune(compose(P,compose(Q,T)))
    for K in range(16):
        for B in range(7): assert accept(P,K,B)==accept(prune(P),K,B)
P={(1,0),(0,1)}; Q={(1,0)}
assert accept(compose(P,Q),1,1)
assert not compose({(1,0)},Q) # cheapest-only and endpoint-only failures
sizes=[]
for m in range(9):
    paths=frozenset({(0,0)})
    for i in range(m): paths=compose(paths,{(1<<i,0),(0,1)})
    assert len(paths)==len(prune(paths))==2**m
    for p in paths:
        assert accept(paths,*p) and not accept(paths-{p},*p)
    sizes.append(len(paths))
print(json.dumps({'status':'passed','exhaustive_family_pairs':len(families)**2,
 'exhaustive_family_triples':len(small)**3,'random_triples':3000,
 'antichain_sizes_m_0_to_8':sizes},indent=2))
