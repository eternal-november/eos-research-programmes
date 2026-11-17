#!/usr/bin/env python3
"""Exact finite discriminators, not universal/native-recursion proofs."""
from fractions import Fraction as F
from itertools import product, permutations
import json

def raw_lift(W, f, sp, tp):
    maps=[]
    for p,q in zip(sp,tp):
        d={}
        for w in W:
            h,k=p(w),q(f(w))
            if h in d and d[h]!=k:return None
            d[h]=k
        maps.append(d)
    return maps
W=list(product(range(2),repeat=2))
p=[lambda w:(),lambda w:w[:1],lambda w:w]
assert raw_lift(W,lambda w:w,p,p) is not None
assert raw_lift(W,lambda w:w[::-1],p,p) is None
# Exhaustively count all law-preserving bijections of the uniform two-bit row.
causal=0
for perm in permutations(W):
    f=dict(zip(W,perm))
    causal+=raw_lift(W,f.__getitem__,p,p) is not None
assert causal==8 and len(list(permutations(W)))==24
# Causal weak map, not pointwise strong: source reveals x then repeats it.
S=[(0,0),(1,1)]; f=lambda w:('*',w[1])
assert raw_lift(S,f,p,p) is not None
for x in range(2):
    source_push={x:F(1)};target={0:F(1,2),1:F(1,2)}
    assert source_push!=target
assert {i:sum(F(1,2) for w in S if f(w)[1]==i) for i in range(2)}==target
# Zero source prefix has a prescribed deterministic service, positive target is fair.
source_mass={'s0':F(0),'s1':F(1,2),'s2':F(1,2)}
services={'s0':{0:F(1),1:F(0)},'s1':target,'s2':target}
average={i:sum(source_mass[h]*services[h][i] for h in source_mass) for i in (0,1)}
assert average==target and services['s0']!=target

def rank(a):
    a=[list(map(F,r)) for r in a]; n=len(a);m=len(a[0]);i=0
    for j in range(m):
        k=next((k for k in range(i,n) if a[k][j]),None)
        if k is None:continue
        a[i],a[k]=a[k],a[i];d=a[i][j];a[i]=[x/d for x in a[i]]
        for k in range(n):
            if k!=i:
                d=a[k][j];a[k]=[x-d*y for x,y in zip(a[k],a[i])]
        i+=1
    return i
R=[[1,0,0],[0,1,0]];A_bad=[[1,0,0],[0,1,1]];A_good=[[1,0,0],[1,1,0]]
assert rank(R)==2 and rank(R+A_bad)==3 and rank(R+A_good)==2
# Cross-completion consistency is independent of individual surjectivity.
R2=[[1,1]];A2=[[1,2]]
assert rank(R2)==1 and rank(R2+A2)==2
# Equal restrictions and comparison identities do not force equal forward updates.
source_insert=(F(1),F(0));target_insert=(F(1),F(1))
assert source_insert[0]==target_insert[0] and source_insert!=target_insert
# Joint generation matters: end data cannot see the second prefix coordinate.
R3=[[1],[0]]
assert rank(R3)==1<2
# Every raw binary prefix has a legal stop extension. Two full-simplex
# deterministic services never choose stop, but choose different continued bits.
def finite_unfold(bit,depth):
    live={():F(1)};stopped={}
    for _ in range(depth):
        new={}
        for prefix,mass in live.items():
            stopped[prefix+('stop',)]=mass*F(0)
            for outcome in (0,1):
                new[prefix+(outcome,)]=mass*F(int(outcome==bit))
        live=new
    return live,stopped
left,sl=finite_unfold(0,5);right,sr=finite_unfold(1,5)
assert sl==sr and all(v==0 for v in sl.values())
assert sum(left.values())==sum(right.values())==1
assert sum(v for h,v in left.items() if h[0]==0)==1
assert sum(v for h,v in right.items() if h[0]==0)==0
print(json.dumps({'status':'PASS','uniform_terminal_permutations':24,'causal_terminal_permutations':causal,'swap':'fails raw prefix factorization','causal_weak_map':'fails strong service square','zero_table':'whole-law average passes, zero source pointwise square fails','material_bad_stacked_rank':3,'material_source_rank':2,'material_good_stacked_rank':2,'cross_completion_consistency':'fails despite individual surjectivity','non_joint_generation':'uniqueness not inferred','scope':'exact finite diagnostics; no universal proof or formal certification'},indent=2))
