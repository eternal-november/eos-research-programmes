#!/usr/bin/env python3
"""Independent adversarial tests, importing but not modifying author's checker."""
import importlib.util, itertools, json, pathlib, random
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('theory_checker',ROOT/'theory/check_relational_discovery.py')
t=importlib.util.module_from_spec(spec);spec.loader.exec_module(t)
H=t.catalogue(3,2); contexts=list(itertools.product(range(3),repeat=3)); actions=list(itertools.product((0,1),repeat=3))
rng=random.Random(103019);cases=0
# Unresolved candidate union, not just a single-hypothesis observer.
for _ in range(200):
    P=rng.sample(H,rng.randrange(1,15));caps={}
    for h in P:
        for j,l in t.scope(h).items():caps[j]=max(caps.get(j,0),l)
    for c in contexts:
        q=tuple(min(c[j],caps.get(j,0)) for j in range(3))
        assert all(t.ev(h,c)==t.ev(h,q) for h in P)
        for a in actions:
            cp=tuple(min(2,x+1) if u else 0 for x,u in zip(c,a))
            qp=tuple(min(caps.get(j,0),q[j]+1) if a[j] else 0 for j in range(3))
            assert qp==tuple(min(cp[j],caps.get(j,0)) for j in range(3))
            cases+=1
    small=rng.sample(P,rng.randrange(1,len(P)+1)); sc={}
    for h in small:
        for j,l in t.scope(h).items():sc[j]=max(sc.get(j,0),l)
    for c in contexts:
        old=tuple(min(c[j],caps.get(j,0)) for j in range(3))
        assert tuple(min(old[j],sc.get(j,0)) for j in range(3))==tuple(min(c[j],sc.get(j,0)) for j in range(3))
# Every binary relation obtainable from repeated sum rows on constants; all forests
# on four nodes with every edge label 0,1,2. Include disconnected contradiction.
const=[('c',0),('c',1)]; edges=list(itertools.combinations(range(4),2));tested=0
for labels in itertools.product((-1,0,1,2),repeat=len(edges)):
    E={e:[((0,0,0),(0,0,0),s)] for e,s in zip(edges,labels) if s>=0}
    try:P,_=t.forest_projection([const]*4,E)
    except ValueError:continue
    W,Q=t.brute([const]*4,E);assert P==Q;tested+=1
E={(0,1):[((0,0,0),(0,0,0),0),((0,0,0),(0,0,0),2)]}
assert t.forest_projection([const]*4,E)[0]==[set()]*4
# Global extendibility does NOT license joint combinations. All variables in XOR
# chain have both values supported, but endpoints must agree.
E={(0,1):[((0,0,0),(0,0,0),1)],(1,2):[((0,0,0),(0,0,0),1)]}
W,P=t.brute([const]*3,E)
assert all(len(x)==2 for x in P) and len(W)==2
assert not any(w[0]!=w[2] for w in W)
assert any(w[0]!=w[2] for w in itertools.product(*P))
# Rejoining: equal boundary marginal cannot recover internal conditional identity.
Eeq={(0,1):[((0,0,0),(0,0,0),0)]}
# Two couplings with identical boundary projection but opposite internal mapping.
R_equal={(0,0),(1,1)};R_unequal={(0,1),(1,0)}
assert {b for a,b in R_equal}=={b for a,b in R_unequal}
assert {a for a,b in R_equal if b==0}!={a for a,b in R_unequal if b==0}
out={'status':'PASS','unresolved_union_observer_updates':cases,'exhaustive_constant_forests':tested,'disconnected_unsat_global_projection':True,'globally_extendible_not_jointly_compatible':True,'boundary_marginal_insufficient_to_rejoin':True,'limitations':'Tests are finite. Physical acquisition, mission search and module witnesses require separate experiment validation.'}
(ROOT/'review/independent_theory_tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
