"""Independent multiplicity-factor tests; does not decide general integer rank."""
from itertools import product
import json

def mm(A,B):
 return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
matrices=[[[a,b],[c,d]] for a,b,c,d in product(range(2),repeat=4)]
checks=0
for p in product(range(3),repeat=2):
 for q in product(range(3),repeat=2):
  P=[[p[0]],[p[1]]]; Q=[list(q)]; A=mm(P,Q)
  # Compose actual labelled witnesses through a single intermediate value.
  witnesses=[(i,j,a,b) for i,j in product(range(2),repeat=2) for a in range(p[i]) for b in range(q[j])]
  assert A==[[sum(w[:2]==(i,j) for w in witnesses) for j in range(2)] for i in range(2)]
  for L,R in product(matrices,repeat=2):
   assert mm(mm(L,A),R)==mm(mm(L,P),mm(Q,R));checks+=1
  for f,g in product(product(range(2),repeat=2),repeat=2):
   restricted=[[A[f[i]][g[j]] for j in range(2)] for i in range(2)]
   assert restricted==mm([[p[f[0]]],[p[f[1]]]],[list(q[g[j]] for j in range(2))]);checks+=1
# Boolean rank one need not imply multiplicity-factor rank one.
A=[[1,1],[1,2]]
assert all(x>0 for row in A for x in row)
assert A[0][0]*A[1][1]-A[0][1]*A[1][0]!=0
# Rank at most two is explicit over N0.
assert mm([[1,0],[0,1]],A)==A
print(json.dumps({'factor_preservation_checks':checks,'witness_multiplicity_cases':81,'boolean_rank_insufficiency':'PASS','status':'PASS'},indent=2))
