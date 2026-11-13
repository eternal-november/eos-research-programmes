#!/usr/bin/env python3
"""Exact finite structural controls; not a replacement for a general proof."""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
import json

def push(law, fn):
    out = defaultdict(F)
    for x,p in law.items(): out[fn(x)] += p
    return dict(out)

def tensor(*laws):
    ans = {}
    for xs in product(*[list(law) for law in laws]):
        p = F(1)
        for law,x in zip(laws,xs): p *= law[x]
        ans[xs] = p
    return ans

coin = {0:F(1,2),1:F(1,2)}
four = {i:F(1,4) for i in range(4)}
assert push(four, lambda x:x%2)==coin

# A prior sample chooses binary versus unary output, so the later context
# really changes cardinality. Content merges these shapes to unary, retaining
# first/only occurrence. The b1 context cell is the noninvertible parity map.
source = {}
for rs,p in tensor(coin,four).items(): source[(0,rs)] = F(1,2)*p
for rs,p in tensor(four).items(): source[(1,rs)] = F(1,2)*p
def mixed_cell(x):
    prior,rs = x
    return (prior, rs[0] if prior==0 else rs[0]%2)
target = {(prior,r):F(1,4) for prior in (0,1) for r in (0,1)}
assert len(source)==12 and len(target)==4
assert sum(source.values())==1
assert push(source,mixed_cell)==target

# Two parallel content grade cells select first or second occurrence. After
# a noninjective base map identifying their labels, they still have distinct
# retained witness maps. No occurrence merges under pure base relabeling.
pair = tensor(coin,coin)
first = lambda rs:rs[0]
second = lambda rs:rs[1]
assert push(pair,first)==push(pair,second)==coin
assert first((0,1)) != second((0,1))
labels = ("b0","b1")
v = {"b0":"c","b1":"c"}
for rs in pair:
    # Q(e_v) chi = chi (Q(v), identity-on-occurrence-coordinates).
    left = tuple((v[b],r) for b,r in zip(labels,rs))
    right = tuple((b,r) for b,r in zip(tuple(v[b] for b in labels),rs))
    assert left==right
    assert len(left)==2

# Forbidden duplication: h:{0,1}->{0} induces diagonal, not product law.
diagonal = push(coin,lambda x:(x,x))
assert diagonal != pair
assert sum(p for (x,y),p in diagonal.items() if x==y)==1
assert sum(p for (x,y),p in pair.items() if x==y)==F(1,2)

# Dependent sum/product distributivity, followed by an affine deletion.
# Each local pair (r,s) is sampled in two stages; r changes the second carrier.
local = {}
for r,pr in coin.items():
    for s in range(r+1): local[(r,s)] = pr*F(1,r+1)
joint = tensor(local,local)
flatten = lambda pairs: ((pairs[0][0],pairs[1][0]),(pairs[0][1],pairs[1][1]))
rebracketed = push(joint,flatten)
expected = {}
for rs,pr in tensor(coin,coin).items():
    for ss in product(*[range(r+1) for r in rs]):
        p = pr
        for r in rs:p *= F(1,r+1)
        expected[(rs,ss)] = p
assert rebracketed==expected
assert push(joint,lambda pairs:pairs[1])==local
assert push(rebracketed,lambda x:(x[0][1],x[1][1]))==local

# Boolean-semiring full-support analogue: affine coordinate maps are onto
# possibility supports, whereas duplicate-coordinate image misses off-diagonal.
poss = {0,1}
poss_pair = set(product(poss,poss))
assert {x for x,y in poss_pair}==poss
assert {y for x,y in poss_pair}==poss
assert {(x,x) for x in poss} != poss_pair

print(json.dumps({
 "status":"passed",
 "mixed_source_points":len(source),"mixed_target_points":len(target),
 "dependent_law_source_points":len(joint),
 "checks":["dependent shape merge and parity cell","parallel content cells retained",
           "noninjective base relabeling preserves occurrences",
           "duplication obstruction","dependent product/sum law with deletion",
           "Boolean possibility-support analogue"],
 "scope":"exact finite controls; general arguments and limits in O1_Feasibility_and_Scope_Decision.tex"
},indent=2))
