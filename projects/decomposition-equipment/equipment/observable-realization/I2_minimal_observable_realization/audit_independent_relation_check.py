#!/usr/bin/env python3
"""Auditor-authored direct exhaustive check, importing no constructor code."""
import itertools as it
import json
G=list(it.product(range(4),repeat=2)); Q=list(it.product(range(2),repeat=2))
def obs(x): return (x[0]%2,x[1]%2)
def minus(x,a,m): return tuple((v-w)%m for v,w in zip(x,a))
def plus(a,b,m): return tuple((v+w)%m for v,w in zip(a,b))
modal=0
for x in G:
    assert obs(x)[0]==x[0]%2
    assert obs((x[1],x[0]))==tuple(reversed(obs(x)))
    for a in G: assert obs(plus(x,a,4))==plus(obs(x),obs(a),2)
    for maskA,maskB in it.product(range(16),repeat=2):
        A={q for i,q in enumerate(Q) if maskA>>i&1}
        B={q for i,q in enumerate(Q) if maskB>>i&1}
        concrete=any(obs(a) in A and obs(minus(x,a,4)) in B for a in G)
        abstract=any(a in A and minus(obs(x),a,2) in B for a in Q)
        assert concrete==abstract
        modal+=1
shared=0
for x,y in it.product(G,repeat=2):
    concrete={(obs(a),obs(minus(x,a,4)),obs(minus(y,a,4))) for a in G}
    abstract={(a,minus(obs(x),a,2),minus(obs(y),a,2)) for a in Q}
    assert concrete==abstract
    shared+=1
print(json.dumps({'scope':'independent C4^2 to C2^2 coefficient check, no old-skeleton engine',
                  'all_unary_source_boolean_factor_predicate_cases':modal,
                  'all_rank_two_shared_parent_sources':shared,'result':'PASS'},indent=2))
