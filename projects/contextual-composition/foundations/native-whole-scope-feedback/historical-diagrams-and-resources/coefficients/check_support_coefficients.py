"""Exact finite witnesses; not a proof of naturality or integrated semantics."""
from fractions import Fraction as Q
import json

def matrix(rows):
    return [[Q(x) for x in row] for row in rows]
def mul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def sub(a,b):
    return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def identity(n):
    return matrix([[int(i==j) for j in range(n)] for i in range(n)])
def kron(a,b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]
def rank(a):
    a=[r[:] for r in a]; k=0
    for j in range(len(a[0])):
        i=next((i for i in range(k,len(a)) if a[i][j]),None)
        if i is None: continue
        a[k],a[i]=a[i],a[k]
        d=a[k][j]; a[k]=[x/d for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                d=a[i][j]; a[i]=[x-d*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a): break
    return k

I2=identity(2); eps=matrix([[1,0]])
# Cross-episode identity relation with individually fixed old marginal legs.
pA=kron(I2,eps); pB=kron(eps,I2); defect=sub(pA,pB)
# E basis: e00, e01+e10, e11.
E=matrix([[1,0,0],[0,1,0],[0,1,0],[0,0,1]])
assert rank(defect)==1 and rank(E)==3
assert mul(defect,E)==matrix([[0,0,0],[0,0,0]])
u=mul(pA,E)
assert u==mul(pB,E) and rank(u)==2
assert mul(pA,matrix([[0],[0],[1],[0]])) != mul(pB,matrix([[0],[0],[1],[0]]))
# The joint observer erases retained source material; no r with r*u=E exists.
lost=matrix([[0],[0],[1]])
assert mul(u,lost)==matrix([[0],[0]])
assert mul(E,lost)==matrix([[0],[0],[0],[1]])
# Treat B as increment: historical E has restriction pA*E to old A.
# A following unrestricted increment N retains E tensor N, and restrictions compose.
rho=mul(pA,E)
second_restriction=kron(identity(3),eps)
assert mul(rho,second_restriction)==mul(kron(pA,eps),kron(E,I2))

# Strict changing-target parallel-edge shape. At M=Q^2, limit inclusion
# is e0 tensor identity; after insertion L=Q^2 it is e0 tensor I4.
f=matrix([[1,0],[0,0]]); g=I2; e0=matrix([[1],[0]])
old_leg=kron(e0,I2); new_leg=kron(e0,identity(4))
assert mul(sub(kron(f,I2),kron(g,I2)),old_leg)==matrix([[0,0],[0,0],[0,0],[0,0]])
assert mul(sub(kron(f,identity(4)),kron(g,identity(4))),new_leg)==[[Q(0)]*4 for _ in range(8)]
insert=identity(4); restriction=kron(I2,eps)
assert mul(restriction,insert)==kron(I2,eps)
assert mul(new_leg,insert)==kron(old_leg,I2)
# A nontrivial augmented slot map, tested through insertion and restriction.
h=matrix([[1,0],[3,2]])
assert mul(kron(h,I2),insert)==mul(insert,kron(h,I2))
assert mul(restriction,kron(h,I2))==mul(h,restriction)

report={
  'field':'Q; Fraction arithmetic',
  'cross_episode_source_dimension':4,
  'cross_episode_compatibility_rank':rank(defect),
  'maximal_compatible_domain_dimension':rank(E),
  'joint_limit_dimension':2,
  'compatible_update_kernel_dimension':rank(E)-rank(u),
  'joint_only_prefix_restriction':'obstructed by explicit lost vector',
  'history_retaining_two_step_restriction':'passed',
  'changing_node_equalizer_dimension_before':2,
  'changing_node_equalizer_dimension_after':4,
  'insertion_restriction_and_augmented_slot_squares':'passed',
  'scope':'finite exact witnesses only; not formal verification of universal claims'
}
print(json.dumps(report,indent=2))
