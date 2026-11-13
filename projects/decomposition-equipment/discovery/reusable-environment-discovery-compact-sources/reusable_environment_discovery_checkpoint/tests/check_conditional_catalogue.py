"""Exact population-table test of unknown block/scope catalogue and augmentation.
Nonadditive stochastic controlled kernel. This is a finite theorem regression,
not a finite-data demonstration or a proof of the general theorem.
"""
from fractions import Fraction as F
from itertools import combinations,product
import json
n=3
contexts=list(product((0,1),repeat=n)); outputs=contexts
subsets=[S for s in (1,2) for S in combinations(range(n),s)]
scopes=[()]+[(i,) for i in range(n)]
augment=[()]+subsets
partitions=[((0,),(1,),(2,)),((0,1),(2,)),((0,2),(1,)),((1,2),(0,))]

def marginal(p,S):
 r={y:F(0) for y in product((0,1),repeat=len(S))}
 for y,v in p.items():r[tuple(y[i] for i in S)]+=v
 return r

def true(x):
 # Nonadditive noise: correlation of output0/output1 flips with action0.
 # All single marginals0/1 remain fair. Output2 responds stochastically to action2.
 p={}
 for y in outputs:
  pair=F(3,8) if (y[0]^y[1])==x[0] else F(1,8)
  p[y]=pair*(F(3,4) if y[2]==x[2] else F(1,4))
 assert sum(p.values())==1
 return p
P={x:true(x) for x in contexts}
cache={}
def conditional(S,W,c):
 key=(S,W,c)
 if key not in cache:
  xs=[x for x in contexts if tuple(x[i] for i in W)==c]
  r={y:F(0) for y in product((0,1),repeat=len(S))}
  for x in xs:
   for y,v in marginal(P[x],S).items():r[y]+=v/len(xs)
  cache[key]=r
 return cache[key]

def candidate(pi,us):
 q={}
 for x in contexts:
  laws=[conditional(B,U,tuple(x[i] for i in U)) for B,U in zip(pi,us)]
  q[x]={}
  for y in outputs:
   z=F(1)
   for B,law in zip(pi,laws):z*=law[tuple(y[i] for i in B)]
   q[x][y]=z
 return q

def passes(pi,us,Q):
 for S in subsets:
  U=tuple(sorted(set().union(*(set(u) for B,u in zip(pi,us) if set(B)&set(S)))))
  for V in augment:
   W=tuple(sorted(set(U)|set(V)))
   for x in contexts:
    if marginal(Q[x],S)!=conditional(S,W,tuple(x[i] for i in W)):return False
 return True
count=accepted=0
for pi in partitions:
 for us in product(scopes,repeat=len(pi)):
  Q=candidate(pi,us);ok=passes(pi,us,Q)
  equal=all(P[x]==Q[x] for x in contexts)
  assert ok==equal
  count+=1;accepted+=ok
assert accepted>0
# All-singleton candidate matches all per-coordinate conditional kernels,
# yet destroys action-dependent pair correlation. Joint tests detect it.
pi=partitions[0];us=((),(),(2,));Q=candidate(pi,us)
assert all(marginal(P[x],(i,))==marginal(Q[x],(i,)) for x in contexts for i in range(n))
assert not passes(pi,us,Q)
assert any(P[x]!=Q[x] for x in contexts)
print(json.dumps({'status':'PASS','catalogue_candidates':count,
 'accepted_exact_joint_laws':accepted,'all_acceptances_equal_true_controlled_kernel':True,
 'singleton_only_false_model_rejected_by_joint_tests':True},indent=2))
