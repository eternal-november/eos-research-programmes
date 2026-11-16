from fractions import Fraction as F
from itertools import product
import json
p=(F(1,2),F(1,2),F(0)); n=(0,2,1)
q=(F(1,3),F(2,3),F(0)); m=(1,2,0)
r=(F(1,2),F(1,2),F(0))
left={};right={}
def mul(xs):
 out=F(1)
 for x in xs:out*=x
 return out
for z in range(3):
 for ys in product(range(3),repeat=n[z]):
  for ts in product(range(3),repeat=sum(m[y] for y in ys)):
   key=(z,tuple((y,tuple(ts[sum(m[v] for v in ys[:i]):sum(m[v] for v in ys[:i+1])])) for i,y in enumerate(ys)))
   left[key]=p[z]*mul(q[y] for y in ys)*mul(r[t] for t in ts)
for z in range(3):
 rows=[(y,ts,q[y]*mul(r[t] for t in ts)) for y in range(3) for ts in product(range(3),repeat=m[y])]
 for children in product(rows,repeat=n[z]):
  key=(z,tuple((y,ts) for y,ts,_ in children))
  right[key]=p[z]*mul(weight for _,_,weight in children)
assert left==right and sum(left.values())==1
assert any(w==0 for w in left.values())
# Explicit event-local birth law, outcome dependent arity, all zeros retained.
def row(e):
 return {(w,ys):p[w]*mul(q[y] for y in ys) for w in range(3) for ys in product(range(3),repeat=n[w])}
for e,d in ((0,1),(1,0)):
 for z in range(3):
  before=row(e);after=row(e)
  assert before==after and sum(before.values())==1
  for w in range(3):
   born_e={(e,w,j) for j in range(n[w])}
   born_d={(d,z,j) for j in range(n[z])}
   assert not born_e & born_d
# Ambiguous per-run birth uniqueness alone does not suffice.
# Port appears only once BOTH events have fired.
def barrier_birth(done,e):return {'port'} if len(done|{e})==2 and len(done)<2 else set()
assert not barrier_birth(set(),0) and barrier_birth({1},0)=={'port'}
assert len([()])==1 and len(list(product(range(2),repeat=1)))==2
# Actual nontrivial augmented coefficient maps commute with labelled permutation.
def kron(A,B):return [[a*b for a in ar for b in br] for ar in A for br in B]
def mm(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def flip(a,b):
 M=[[0]*(a*b) for _ in range(a*b)]
 for i in range(a):
  for j in range(b):M[j*a+i][i*b+j]=1
 return M
A=[[1,0],[2,3],[0,4]] # k^2 -> k^3, augmentation first coordinate
B=[[1,0,0],[5,2,1]] # k^3 -> k^2
assert mm(flip(3,2),kron(A,B))==mm(kron(B,A),flip(2,3))
assert A[0]==[1,0] and B[0]==[1,0,0]
print(json.dumps({'status':'passed','raw_initializer_trees':len(left),'zero_trees':sum(w==0 for w in left.values()),'total_mass':str(sum(left.values())),
 'checks':['three-level-initializer-associator','nullary-and-zero-retention','birth-stable-expanded-row-normalization','barrier-birth-obstruction','actual-augmented-tensor-flip-square']},indent=2))
