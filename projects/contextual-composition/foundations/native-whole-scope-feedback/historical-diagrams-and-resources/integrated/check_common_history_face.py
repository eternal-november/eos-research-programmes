#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
import json

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
I=[[int(i==j) for j in range(9)] for i in range(9)]
indices=[0,1,3,4,2,6,8];face=[I[i] for i in indices]
assert rank(face)==7
repair=I[5]
assert rank(face+[repair])==8 # repair fails quotient descent
# H is graph of the witness x5 and is identified with the full nine coordinates.
# Product J x_Q H uses J's seven coordinates and H's eight nonaugmentation ones.
obs=face+I[1:]
assert len(obs)==15 and rank(obs)==9
# Source product K x_Q H uses 9+8 coordinates. Its face to target picks the
# old joint's seven coordinates and leaves H's last eight coordinates literal.
source_obs=I+I[1:]
map_indices=indices+list(range(9,17))
assert [source_obs[i] for i in map_indices]==obs
# Old historical restriction is identity for the unit resource and graph.
assert I[5]==repair and face[0]==I[0]
rows=list(product((0,1),repeat=4))
independent={r:F(1,16) for r in rows}
swap={r:(F(1,4) if r[2]==r[1] and r[3]==r[0] else F(0)) for r in rows}
def fair(q,which,full):
 for vals in product((0,1),repeat=2 if full else 1):
  def matches(r):return r[:2]==vals if full else r[which]==vals[0]
  mass=sum(v for r,v in q.items() if matches(r))
  for y in (0,1):
   assert mass>0
   if sum(v for r,v in q.items() if matches(r) and r[2+which]==y)!=mass/2:return False
 return True
assert all(fair(independent,i,True) and fair(independent,i,False) for i in (0,1))
assert all(fair(swap,i,False) and not fair(swap,i,True) for i in (0,1))
print(json.dumps({'status':'PASS','whole_scope_history_dimension':9,'target_joint_dimension':7,'face_rank':7,'face_kernel_dimension':2,'repair_descent_stacked_rank':8,'enriched_target_joint_dimension':15,'retained_history_observer_rank':9,'product_face_observer_square':True,'independent_joint_admitted_both':True,'target_admission_strictly_larger':True,'scope':'finite rational matrix and conditional-law witnesses; no universal or recurrent formal proof'},indent=2))
