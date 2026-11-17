#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
import json

def mm(a,b):
 return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def kron(a,b):
 return [[x*y for x in rowa for y in rowb] for rowa in a for rowb in b]
def lift(n,t,extra):
 return [[F(t*int(i==j)) for j in range(n)] for i in range(n)]+[[F(x) for x in extra]]
def proj(n):return [[F(int(i==j)) for j in range(n+1)] for i in range(n)]
def eye(n,t=1):return [[F(t*int(i==j)) for j in range(n)] for i in range(n)]
count=0
for t,a,t1,a1 in product((-1,0,1),repeat=4):
 S=lift(2,t,[1,-2]);T=lift(3,a,[2,0,-1]);U=lift(1,t1,[3]);V=lift(2,a1,[1,2])
 assert mm(proj(2),S)==eye(2,t)
 assert mm(proj(3),T)==eye(3,a)
 assert mm(kron(T,V),kron(S,U))==kron(mm(T,S),mm(V,U))
 assert mm(mm(proj(2),proj(3)),mm(T,S))==eye(2,t*a)
 for z in (1,2,3):assert mm(kron(proj(2),eye(z)),kron(S,eye(z)))==eye(2*z,t)
 count+=1
# Three-stage resource composition is strict at evaluated joint operators.
S=lift(2,1,[2,3]);T=lift(3,1,[1,-1,0]);U=lift(4,1,[2,0,1,4])
assert mm(U,mm(T,S))==mm(mm(U,T),S)
# Historical universal normalization kills a direction an actual augmented reader sees.
phi=[[F(1),F(0)]];d=eye(2);hidden=[[F(0)],[F(1)]]
assert mm(phi,hidden)==[[0]] and mm(d,hidden)==hidden
# Every declared joint-local reader passes, including a nontrivial extra output.
reader=[[F(1)],[F(3)]];actual=mm(reader,phi)
assert mm(actual,hidden)==[[0],[0]]
# A second normalized resource is retained; prefix square uses its augmentation.
psi=[[F(1),F(0),F(0)]]
F2=kron(phi,psi)
source_restrict=kron(eye(2),psi)
target_restrict=[[F(1)]]
assert mm(target_restrict,F2)==mm(phi,source_restrict)
print(json.dumps({'status':'PASS','tensor_sequential_interchange_cases':count,'framing_dimensions':[1,2,3],'three_stage_associativity':True,'historical_consumer_obstruction':'nonzero hidden vector killed by forced normalization','joint_local_reader_square':True,'two_step_prefix_square':True,'scope':'exact rational finite witnesses; no universal/recurrent proof certification'},indent=2))
