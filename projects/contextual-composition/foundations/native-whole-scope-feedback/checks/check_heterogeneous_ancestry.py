from itertools import product
from fractions import Fraction as F
import json
# Fixed finite raw carrier: root P z=0 has no U child; z=1 has one.
# Root Q q always exists; child P x=1 produces child Q y, x=0 has no y.
raw=[(0,0,None,None),(0,1,None,None),(1,0,0,None),(1,1,0,None),
     (1,0,1,0),(1,0,1,1),(1,1,1,0),(1,1,1,1)]
def comp(n,k):
    if k==1:yield (n,);return
    for i in range(n+1):
        for tail in comp(n-i,k-1):yield (i,)+tail
def mass(cs,pred):return sum(c for a,c in zip(raw,cs) if pred(a))
def fair(cs,cond,coord):
    den=mass(cs,cond)
    return den==0 or all(2*mass(cs,lambda a,b=b:cond(a) and a[coord]==b)==den for b in (0,1))
def ancestral(cs):
    return fair(cs,lambda a:True,0) and all(fair(cs,lambda a,z=z:a[0]==z,1) for z in (0,1)) and fair(cs,lambda a:a[0]==1,2) and fair(cs,lambda a:a[0]==1 and a[2]==1,3)
def grouped(cs):
    # Independently form root+complete-child law, then test recursive child family.
    root={z:sum(c for a,c in zip(raw,cs) if a[0]==z) for z in (0,1)}
    if root[0]!=root[1]:return False
    for z in (0,1):
        if root[z]:
            qlaw={q:F(sum(c for a,c in zip(raw,cs) if a[0]==z and a[1]==q),root[z]) for q in (0,1)}
            if qlaw!={0:F(1,2),1:F(1,2)}:return False
    if root[1]:
        child={t:F(sum(c for a,c in zip(raw,cs) if a[0]==1 and (a[2],a[3])==t),root[1]) for t in [(0,None),(1,0),(1,1)]}
        if child[(0,None)]!=F(1,2):return False
        x1=child[(1,0)]+child[(1,1)]
        if x1 and child[(1,0)]/x1!=F(1,2):return False
    return True
def left(cs):
    # Q seeds conditional complete P tree; both Q marginals, not independence.
    return fair(cs,lambda a:True,0) and fair(cs,lambda a:a[0]==1,2) and fair(cs,lambda a:a[0]==0,1) and all(fair(cs,lambda a,x=x:a[0]==1 and a[2]==x,1) for x in (0,1)) and fair(cs,lambda a:a[0]==1 and a[2]==1,3)
def right(cs):
    # Recursive composite child law conditioned on root Q as well as root P.
    return fair(cs,lambda a:True,0) and all(fair(cs,lambda a,z=z:a[0]==z,1) for z in (0,1)) and all(fair(cs,lambda a,q=q:a[0]==1 and a[1]==q,2) for q in (0,1)) and all(fair(cs,lambda a,q=q:a[0]==1 and a[1]==q and a[2]==1,3) for q in (0,1))
counts={'N':0,'L':0,'R':0};total=0
for tail in comp(8,6):
    cs=(4,4)+tail;total+=1
    n=ancestral(cs);assert n==grouped(cs)
    l=left(cs);r=right(cs)
    assert not l or n
    assert not r or n
    counts['N']+=n;counts['L']+=l;counts['R']+=r
assert counts=={'N':9,'L':3,'R':1}
# A common-runtime law outside both source subsets on this finite slice.
w=(4,4,4,0,0,0,2,2)
assert ancestral(w) and not left(w) and not right(w)
# Distinguished product initializer lies in all three and has variable absence.
dist=(4,4,2,2,1,1,1,1)
assert ancestral(dist) and left(dist) and right(dist)
# Zero atoms are not pruned even in the outside-both witness.
assert len(w)==8 and sum(c==0 for c in w)==3
print(json.dumps({'variable_request_raw_atoms':8,'integer_laws_tested':total,'denominator':16,'ancestral_vs_grouped_tests':'PASS','source_L_and_R_law_inclusions':'PASS','admitted_counts_on_test_slice':counts,'N_outside_both_source_images':'PASS','distinguished_independent_member':'PASS','scope':'finite exact initial-law diagnostics; general induction and paid inclusion remain written proofs'},indent=2))
