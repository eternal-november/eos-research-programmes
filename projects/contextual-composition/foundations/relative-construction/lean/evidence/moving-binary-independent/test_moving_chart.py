"""Finite check of the generic transport rule, not an instance of the Lean project."""
from itertools import product,permutations
P=tuple(permutations(range(3)))
def comp(f,g): return tuple(g[i] for i in f)
def inv(p): return tuple(p.index(i) for i in range(len(p)))
raw=(0,0,2)   # unique generating 0->1 arrow maps noninjectively; no inverse
trials=mutants=0
for l0,l1,r0,r1 in product(P,repeat=4):
    L=comp(comp(l0,raw), inv(l1)); R=comp(comp(r0,raw),inv(r1))
    c0=comp(l0,inv(r0)); c1=comp(l1,inv(r1))
    assert comp(L,c1)==comp(c0,R)
    trials+=1
    if comp(L,c1)!=comp(c0,raw): mutants+=1
assert trials==1296 and 0<mutants<trials
print(f'{trials} moving squares verified, {mutants} failures when the right-side chart on arrows is omitted.')
