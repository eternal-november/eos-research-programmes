#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
import json

def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def rank(a):
 a=[list(map(F,r)) for r in a];i=0
 for j in range(len(a[0])):
  k=next((k for k in range(i,len(a)) if a[k][j]),None)
  if k is None:continue
  a[i],a[k]=a[k],a[i];d=a[i][j];a[i]=[x/d for x in a[i]]
  for k in range(len(a)):
   if k!=i:
    d=a[k][j];a[k]=[x-d*y for x,y in zip(a[k],a[i])]
  i+=1
 return i
I=eye(12);keep=[i for i in range(12) if i not in (9,11)];a=[I[i] for i in keep];d=I[9]
assert rank(a)==10 and rank(a+[d])==11
rho=[[F(j==2*i) for j in range(24)] for i in range(12)]
u=rho+[[F(j==1) for j in range(24)]]
assert rank(u)==13 and rank(rho)==12
# H coordinates are (x_0,...,x_11,e_1); e_0 is constrained to x_9.
assert u[9]==mm([d],rho)[0]
source_obs=rho+u[1:];target_obs=mm(a,rho)+u[1:]
assert len(source_obs)==24 and len(target_obs)==22
assert rank(source_obs)==rank(target_obs)==13
assert [source_obs[i] for i in keep+list(range(12,24))]==target_obs
assert rank(eye(24)+u)==24
assert rank(mm(a,rho))==10
# A nonzero resource-kernel vector survives historical graph storage.
assert all(row[3]==0 for row in u) and eye(24)[3][3]==1
# Local owner insertion matrices, including unit owners/resources.
cases=0
for dims in product((1,2,3),repeat=2):
 for l in (1,2,3):
  for selected in (0,1):
   old=[('u',)]+[('o',i,k) for i,n in enumerate(dims) for k in range(n-1)]
   new=[('u',)]+[('o',i,k) for i,n in enumerate(dims) for k in range(n-1)]+[('w',j) for j in range(l-1)]+[('p',k,j) for k in range(dims[selected]-1) for j in range(l-1)]
   columns=[]
   for o in old:
    for j in range(l):
     if j==0:out=o
     elif o==('u',):out=('w',j-1)
     elif o[1]==selected:out=('p',o[2],j-1)
     else:out=None
     columns.append([F(v==out) for v in new])
   matrix=list(map(list,zip(*columns)))
   assert rank(matrix)==len(new);cases+=1
# Full law over initial reserve, launch and first decision. Zero raws kept.
p=(F(1,2),F(1,4),F(1,4),F(0))
raw=list(product((0,1),(0,1),(0,1),range(4)))
q={h:(F(1,2)*p[h[3]] if (h[1],h[2])==(h[0],1-h[0]) else F(0)) for h in raw}
assert sum(q.values())==1 and len(q)==32
for v in (0,1):assert sum(w for h,w in q.items() if h[1]==v)==F(1,2)
for r in (0,1):
 for j in range(4):assert sum(w for h,w in q.items() if h[0]==r and h[3]==j)==F(1,2)*p[j]
extended={h+('*',):w for h,w in q.items()}
assert {h:extended[h+('*',)] for h in raw}==q
print(json.dumps({'status':'PASS','old_face_rank':10,'repair_descent_stacked_rank':11,'retained_history_dimension':24,'joint_evaluation_rank':13,'joint_evaluation_kernel':11,'enlarged_product_dimensions':[24,22],'enlarged_observer_rank':13,'whole_product_epimorphism':False,'old_leg_ranks':[12,10],'owner_insertion_surjectivity_cases':cases,'all_raw_initial_carrier':32,'singleton_extension_preserves_whole_law':True,'scope':'finite matrices/laws; operational recursion and reflection class require written proof'},indent=2))
