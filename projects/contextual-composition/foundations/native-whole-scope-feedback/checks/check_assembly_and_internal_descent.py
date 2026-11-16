from fractions import Fraction as F
from itertools import product
import json
# Internal missing-middle: source root histories merge; row labels conflict.
D={(0,0):F(1,2),(0,1):F(0),(1,0):F(0),(1,1):F(1,2)}
A={(0,0):F(0),(0,1):F(1,2),(1,0):F(1,2),(1,1):F(0)}
assert D!=A
assert sum(D.values())==sum(A.values())==1
middle_choices=[D,A,{k:(D[k]+A[k])/2 for k in D}]
assert not [q for q in middle_choices if q==D and q==A]
# Collapse both participant carriers: all source chosen rows have one pushforward.
assert {():sum(D.values())}=={():sum(A.values())}=={():F(1)}
# Three active blocks and an empty passive fourth block, nonconstant boundary U.
U=(0,1,2)
Z=list(product(U,(0,1),(0,1),(0,1)))
supp={(0,0,0,0),(0,1,1,1),(1,0,1,0),(1,1,0,1)}
q={z:F(1,4) if z in supp else F(0) for z in Z}
assert len(q)==24 and sum(q.values())==1

def push(law,fn):
    out={}
    for z,v in law.items():
        key=fn(z);out[key]=out.get(key,F(0))+v
    return out

def block(z,i): return (z[0],z[i+1])
nu=push(q,lambda z:z[0])
assert nu=={0:F(1,2),1:F(1,2),2:F(0)}
margs=[push(q,lambda z,i=i:block(z,i)) for i in range(3)]
# q is not the independent product of bits conditional on boundary 0.
assert q[(0,0,0,0)]==F(1,4) != F(1,2)*F(1,2)**3
# Retain passive response u as the fourth block tuple.
def flat_blocks(z):return (block(z,0),block(z,1),block(z,2),z[0])
def recover(t):
    a,b,c,u=t
    assert a[0]==b[0]==c[0]==u
    return (u,a[1],b[1],c[1])
lam=push(q,flat_blocks)
assert push(lam,recover)==q
for i in range(3): assert push(lam,lambda t,i=i:t[i])==margs[i]
assert push(lam,lambda t:t[3])==nu
# Both three-block associations retain whole laws and all zero atoms.
left=push(q,lambda z:((block(z,0),block(z,1)),block(z,2)))
right=push(q,lambda z:(block(z,0),(block(z,1),block(z,2))))
assert push(left,lambda t:(t[0][0][0],t[0][0][1],t[0][1][1],t[1][1]))==q
assert push(right,lambda t:(t[0][0],t[0][1],t[1][0][1],t[1][1][1]))==q
assert len(left)==len(right)==len(Z)
# Entirely passive internal subtree ((A,B),C): A,B carry only same U.
CZ=list(product(U,(0,1)))
cq={z:(F(1,4) if z[0] in (0,1) else F(0)) for z in CZ}
passive_nested=push(cq,lambda z:((z[0],z[0]),z))
assert push(passive_nested,lambda t:t[1])==cq
assert push(passive_nested,lambda t:t[0])=={(0,0):F(1,2),(1,1):F(1,2),(2,2):F(0)}
# Different whole law labels remain distinct even on same raw outcome.
def label(law):return tuple(sorted(law.items()))
assert (label(D),(0,0))!=(label(A),(0,0))
print(json.dumps({'internal_missing_middle':'PASS','correlated_nonproduct_whole_law':'PASS','raw_atoms_including_zeros':len(Z),'boundary_zero_value_retained':2,'empty_passive_block':'PASS','entirely_passive_internal_subtree':'PASS','three_block_reassociation':'PASS','offpolicy_law_labels_distinct':'PASS','scope':'finite exact rational diagnostics, not proof certification'},indent=2))
