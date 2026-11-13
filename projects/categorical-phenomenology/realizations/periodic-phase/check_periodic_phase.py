#!/usr/bin/env python3
"""Exact finite checks for formulas, not a proof of the global topology theorem."""
from fractions import Fraction as F
from itertools import product
import json


def matmul(a, b):
    return [[sum((x*y for x,y in zip(row,col)), F(0)) for col in zip(*b)] for row in a]


def add(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def scale(a,c): return [[c*x for x in row] for row in a]
def diag(a): return [[a[i] if i==j else F(0) for j in range(len(a))] for i in range(len(a))]
def identity(n): return diag([F(1)]*n)
def value(rho, kernels, word):
    for y in word: rho=matmul(rho,kernels[y])
    return sum(rho[0])
def rank(a):
    a=[row[:] for row in a]; out=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(out,len(a)) if a[i][j]),None)
        if pivot is None: continue
        a[out],a[pivot]=a[pivot],a[out]
        a[out]=[x/a[out][j] for x in a[out]]
        for i in range(len(a)):
            if i!=out:
                q=a[i][j]; a[i]=[x-q*y for x,y in zip(a[i],a[out])]
        out+=1
        if out==len(a): break
    return out

Q=[[F(1,2),F(1,2),F(0),F(0),F(0)],
   [F(0),F(0),F(1),F(0),F(0)],
   [F(0),F(0),F(0),F(1),F(0)]]
L=[[F(1),F(0),F(0)],[F(1),F(0),F(0)],
   [F(0),F(1),F(0)],[F(0),F(0),F(1)],
   [F(1,3),F(1,3),F(1,3)]]
Pi=[[F(0),F(1),F(0)],[F(0),F(0),F(1)],[F(1),F(0),F(0)]]
assert matmul(Q,L)==identity(3)
emission={1:[F(1,4),F(1,2),F(3,4)]}
emission[0]=[1-x for x in emission[1]]
M={y:matmul(diag(emission[y]),Pi) for y in [0,1]}
T=matmul(matmul(L,Pi),Q)
N={y:matmul(matmul(L,M[y]),Q) for y in [0,1]}
E={y:[row[0] for row in matmul(L,[[x] for x in emission[y]])] for y in [0,1]}
N_before={y:matmul(diag(E[y]),T) for y in [0,1]}
shifted={y:[emission[y][(j-1)%3] for j in range(3)] for y in [0,1]}
N_after={y:matmul(T,diag([row[0] for row in matmul(L,[[x] for x in shifted[y]])])) for y in [0,1]}
assert N_after==N
assert add(N[0],N[1])==T
assert all(sum(row)==1 and min(row)>=0 for row in T)
w=[[F(1),F(0),F(0)]]; rho=matmul(w,Q)
checks=0
for n in range(8):
    for word in product([0,1],repeat=n):
        target=F(1)
        for j,y in enumerate(word): target*=emission[y][j%3]
        assert value(w,M,word)==target
        assert value(rho,N,word)==target
        assert value(rho,N_before,word)==target
        assert value(rho,N_after,word)==target
        checks+=1
# The tempting unshifted transition-first emission is wrong when initial phase is fixed.
wrong={y:matmul(T,diag(E[y])) for y in [0,1]}
assert value(rho,wrong,(1,))==F(1,2)!=value(rho,N,(1,))==F(1,4)
# Finite observable phase averaging stays at the same native width.
rho_bar=[[F(0)]*5]; cur=rho
for _ in range(3):
    rho_bar=add(rho_bar,scale(cur,F(1,3))); cur=matmul(cur,T)
assert rho_bar==matmul([[F(1,3)]*3],Q)
assert matmul(rho_bar,T)==rho_bar # This particular lift is stationary.
for n in range(5):
    for word in product([0,1],repeat=n):
        shifted_average=sum(value(rho,N,u+word) for r in range(3) for u in product([0,1],repeat=r))/3
        assert value(rho_bar,N,word)==shifted_average
# Initial aligned-block rank is 1, while ordinary rank is 3.
words=[()] + [(y,) for y in [0,1]] + list(product([0,1],repeat=2))
hankel=[[value(w,M,u+v) for v in words] for u in words]
assert rank(hankel)==3
blocks=[()]+list(product([0,1],repeat=3))
assert rank([[value(w,M,u+v) for v in blocks] for u in blocks])==1
# Shifted empirical block map F(q)=suffix marginal tensor first marginal.
def shift_block(q):
    m=len(next(iter(q))); suffix={s:F(0) for s in product([0,1],repeat=m-1)}; first={0:F(0),1:F(0)}
    for s,v in q.items(): suffix[s[1:]]+=v; first[s[0]]+=v
    return {s+(y,):v*first[y] for s,v in suffix.items() for y in [0,1]}
q={s:F(i+1,36) for i,s in enumerate(product([0,1],repeat=3))}
assert sum(q.values())==1
marg=[[sum(v for s,v in q.items() if s[r]==y) for y in [0,1]] for r in range(3)]
q3=q
for _ in range(3): q3=shift_block(q3)
assert q3=={s:marg[0][s[0]]*marg[1][s[1]]*marg[2][s[2]] for s in q}
# Explicit three-symbol temporal order witness.
V=[[F(1,2),F(1,3),F(1,6)], [F(1,6),F(1,2),F(1,3)], [F(1,3),F(1,6),F(1,2)]]
assert rank(V)==3
J=scale(matmul(matmul(list(map(list,zip(*V))),Pi),V),F(1,3))
assert J[0][1]!=J[1][0]
report={"all_checks_passed":True,"word_lift_checks":checks,"ordinary_hankel_rank":rank(hankel),"aligned_block_hankel_rank":1,"wrong_transition_first_probability":str(value(rho,wrong,(1,))),"correct_probability":str(value(rho,N,(1,))),"two_output_order_witness":[str(J[0][1]),str(J[1][0])],"scope":"Exact rational checks of formulas and finite witnesses; not proof of topological lower bounds or infinite-rank implications."}
print(json.dumps(report,indent=2))
