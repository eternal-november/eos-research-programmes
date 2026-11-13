#!/usr/bin/env python3
"""Independent finite checks for relational certificate guardrails, stdlib only."""
from itertools import product
import json

B=(0,1)
def subsets(xs):
    xs=tuple(xs)
    return [frozenset(x for k,x in enumerate(xs) if mask>>k&1)
            for mask in range(1<<len(xs))]
pairs=tuple(product(B,repeat=2)); rels=subsets(pairs)
counts={}
# Complete three-edge path: all 4096 triples of binary relations.
for R,S,T in product(rels,repeat=3):
    actual={(a,b,c,d) for a,b,c,d in product(B,repeat=4)
            if (a,b) in R and (b,c) in S and (c,d) in T}
    left={(a,c) for a,b in R for bb,c in S if b==bb}
    via_left={(a,d) for a,c in left for cc,d in T if c==cc}
    right={(b,d) for b,c in S for cc,d in T if c==cc}
    via_right={(a,d) for a,b in R for bb,d in right if b==bb}
    assert via_left==via_right=={(a,d) for a,b,c,d in actual}
    # Store and verify one backpointer for every actual visible pair.
    for a,d in via_left:
        b,c=next((b,c) for b,c in product(B,repeat=2)
                 if (a,b) in R and (b,c) in S and (c,d) in T)
        assert (a,b,c,d) in actual
counts['path_associativity_and_reconstruction']=len(rels)**3
# Cyclic constraints. A shared variable appears once, never freshened per factor.
for R,S,T in product(rels,repeat=3):
    actual={(a,b,c) for a,b,c in product(B,repeat=3)
            if (a,b) in R and (b,c) in S and (c,a) in T}
    residual={(a,b) for a,b in R if any((b,c) in S and (c,a) in T for c in B)}
    assert residual=={(a,b) for a,b,c in actual}
counts['cycle_exact_elimination']=len(rels)**3
# A pairwise-consistent crossing with no joint assignment.
eq=frozenset({(0,0),(1,1)}); neq=frozenset({(0,1),(1,0)})
assert all({x for x,y in r}==set(B)=={y for x,y in r} for r in (eq,eq,neq))
assert not {(a,b,c) for a,b,c in product(B,repeat=3)
            if (a,b) in eq and (b,c) in eq and (c,a) in neq}
# Joining after forgetting a shared old value invents a solution.
R={0}; T={1}; f={0:0,1:0}
assert not R&T
assert {f[x] for x in R}&{f[x] for x in T}=={0}
# Full continuation signatures distinguish precisely different residual rows.
for n in range(4):
    rows=subsets(range(n))
    signatures={r:tuple(bool(r&t) for t in rows) for r in rows}
    assert len(set(signatures.values()))==len(rows)
counts['context_signature_domains']=4
# Pullback of identity is kernel pair; equality with new identity iff injective.
unit_tests=0
for m in range(4):
    for n in range(1,4):
        for values in product(range(n),repeat=m):
            kp={(x,y) for x,y in product(range(m),repeat=2) if values[x]==values[y]}
            diag={(x,x) for x in range(m)}
            assert (kp==diag)==(len(set(values))==m)
            # Exact endpoint request succeeds iff old values equal.
            for x,y in product(range(m),repeat=2):
                assert ((x,y) in kp)==(values[x]==values[y])
            unit_tests+=1
counts['noninvertible_nullary_maps']=unit_tests
# Direct image is only lax for intersection, with strict examples counted.
strict=0; tests=0
for vals in product(B,repeat=3):
    for R,T in product(subsets(range(3)),repeat=2):
        image=lambda S:{vals[x] for x in S}
        assert image(R&T)<=image(R)&image(T)
        strict+=(image(R&T)!=image(R)&image(T)); tests+=1
assert strict>0
counts['intersection_image_tests']=tests
counts['strict_intersection_failures']=strict
# Eliminating an eventually shared variable can destroy constraints.
assert bool({0}) and bool({1}) and not bool({0}&{1})
# Boundary output cost: path of independent free variables has 2^k tuples.
for k in range(9):
    assert len(tuple(product(B,repeat=k)))==2**k
counts['explicit_boundary_size_cases']=9
print(json.dumps({'status':'PASS','checks':counts},indent=2))
