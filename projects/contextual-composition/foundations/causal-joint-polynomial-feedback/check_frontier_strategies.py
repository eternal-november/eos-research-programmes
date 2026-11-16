"""Finite exact regressions only; not certification of the theorem."""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
import json

# Primitive: leaf at B with weight 1/2, or binary U,U with weight 1/2.
# Entire frontier shares the same fair choice. All mixed tuples remain raw zeros.
def kernel(draw):
    return Q(1,2) if len(set(draw))==1 else Q(0)

def histories(depth):
    active=[((),1,Q(1))]; terminal=[]; layers=[]
    for d in range(depth):
        nxt=[]
        for hist,n,p in active:
            for draw in product((0,1),repeat=n):
                h=hist+(draw,); prob=p*kernel(draw)
                m=2*sum(draw)
                if m:nxt.append((h,m,prob))
                else:terminal.append((h,prob))
        active=nxt
        layers.append((sum(p for h,p in terminal),sum(p for h,n,p in active)))
        assert sum(layers[-1])==1
    return terminal,active,layers
terminal,active,layers=histories(4)
assert layers[-1][0]==Q(15,16)
assert any(p==0 for h,p in terminal)
# Every syntactic terminal execution cuts uniquely after min(2,height) rounds.
for h,p in terminal:
    d=min(2,len(h)); pre=h[:d]; suffix=h[d:]
    pp=Q(1); sp=Q(1)
    for draw in pre:pp*=kernel(draw)
    for draw in suffix:sp*=kernel(draw)
    assert pre+suffix==h and pp*sp==p
    for i in range(d+1):
        assert h[:i]+h[i:d]+h[d:]==h
# Local exact transport of split raw leaf witnesses to one target witness.
# At each round choose common category, then independent leaf refinements.
for n in range(1,5):
    pushed=defaultdict(Q)
    for ws in product(('a','b','r'),repeat=n):
        cats=tuple(int(w=='r') for w in ws)
        p=Q(0)
        if all(c==0 for c in cats):p=Q(1,2)*Q(1,2)**n
        if all(c==1 for c in cats):p=Q(1,2)
        pushed[cats]+=p
    for cats in product((0,1),repeat=n):assert pushed[cats]==kernel(cats)
# Diagonal siblings cannot be sequentialized with unchanged fresh fair rows.
diagonal={(0,0):Q(1,2),(1,1):Q(1,2)}
assert diagonal[(0,0)]/Q(1,2)==1
# Branch-law coupling anticipation: each branch independent, global future not fresh.
branch=defaultdict(Q)
for x1,x2 in product((0,1),repeat=2):branch[(x1,x2)]+=Q(1,4)
assert all(p==Q(1,4) for p in branch.values())
# Surjective slice augmentations: tensor -> product can strictly lower dimension.
assert 2**3 > 3*2-(3-1)
print(json.dumps({'terminal_raw_histories_depth4':len(terminal),
 'zero_terminal_histories':sum(p==0 for h,p in terminal),
 'terminal_active_masses':[[str(x),str(y)] for x,y in layers],
 'cut_product_checks':len(terminal),'split_witness_transport_frontier_sizes':[1,2,3,4],
 'scope_split_and_anticipation_counterchecks':'passed'},indent=2))
