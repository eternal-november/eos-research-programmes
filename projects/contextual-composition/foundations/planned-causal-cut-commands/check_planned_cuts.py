"""Finite exact diagnostics for planned cuts; not proofs of infinite control coherence."""
from itertools import product,combinations_with_replacement,permutations
from math import comb
from fractions import Fraction as F
import json

def marks(h,n):return list(combinations_with_replacement(range(h+1),n))
for h in range(1,7):
    sizes=[len(marks(h,n)) for n in range(6)]
    assert sizes==[comb(h+n,n) for n in range(6)]
    assert all(a<b for a,b in zip(sizes,sizes[1:]))

# Histories r0,e and r1,e have equal global unary shape and differing legal cuts.
raw=[('r0','e'),('r1','e')]
shape=lambda t:len(t)
cut=lambda t:1 if t[0]=='r0' else min(2,len(t))
assert shape(raw[0])==shape(raw[1]) and cut(raw[0])!=cut(raw[1])
# No function from the single unmarked shape can give both marked bodies.
assert len({(shape(t),cut(t)) for t in raw})==2

# Cursor addition has literally the same ordered realized marks.
plan=[0,1,2,2,2,2]
for n,k,l in product(range(3),repeat=3):
    if n+k+l<=len(plan):
        assert plan[:n+k]+plan[n+k:n+k+l]==plan[:n+k+l]
assert plan[:0]!=plan[:1] # empty command versus genuine immediate cut

# Invertible extension criterion on one full marker fibre, including unused tuples.
# Keep the source/target unmarked shape fixed.
D=marks(2,1)
checked=0
for used_count in range(4):
    used=D[:used_count]
    for values in product(D,repeat=used_count):
        partial=dict(zip(used,values))
        extendible=any(all(dict(zip(D,p))[x]==y for x,y in partial.items())
                       for p in permutations(D))
        assert extendible==(len(set(values))==len(values))
        checked+=1

# Distinct raw weights force any finite-prefix mass-preserving permutation to fix lengths.
weights=[F(1,2**n) for n in range(1,7)]
assert len(set(weights))==6
assert [p for p in permutations(range(6)) if all(weights[i]==weights[p[i]] for i in range(6))]==[tuple(range(6))]
print(json.dumps({'status':'passed','marker_sizes_checked':'heights 1..6, cursor counts 0..5','partial_bijection_tests':checked,'cases':['raw-dependent-shape-descent-failure','cursor-associativity','zero-cut-not-empty-command','unused-marker-bijective-extension','unit-raw-weight-rigidity'],'scope':'bounded exact checks; no infinite-history or universal module certification'},indent=2))
