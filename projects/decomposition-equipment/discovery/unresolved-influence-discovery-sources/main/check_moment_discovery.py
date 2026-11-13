#!/usr/bin/env python3
"""Exact rational bounded QA; primary closure works on sparse Walsh polynomials.
Whole-state enumeration below is an independent n=4/n=3 test oracle only.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

def clean(p): return {m:c for m,c in p.items() if c}
def add(p,q,scale=F(1)):
 r=p.copy()
 for m,c in q.items(): r[m]=r.get(m,F(0))+scale*c
 return clean(r)
def mul(p,q):
 r={}
 for m,c in p.items():
  for l,d in q.items(): r[m^l]=r.get(m^l,F(0))+c*d
 return clean(r)
def basis_insert(B,p):
 p=clean(p)
 for pivot,b in sorted(B.items()):
  if pivot in p: p=add(p,b,-p[pivot])
 if not p:return False
 pivot=min(p);z=p[pivot]; B[pivot]={m:c/z for m,c in p.items()};return True

def discover(tasks,T,d):
 B={}; basis_insert(B,{0:F(1)})
 for p in tasks:basis_insert(B,p)
 rounds=0
 while True:
  rounds+=1; before=len(B)
  for p in list(B.values()):
   if any(m.bit_count()>d for m in p):return {'status':'outside_measured_span','basis':B,'rounds':rounds}
  for p in list(B.values()):
   for q in list(B.values()):
    r=mul(p,q)
    if any(m.bit_count()>d for m in r):return {'status':'outside_measured_span','witness':r,'rounds':rounds}
    basis_insert(B,r)
  for p in list(B.values()):
   r={}
   for m,c in p.items():r=add(r,T[m],c)
   if any(m.bit_count()>d for m in r):return {'status':'outside_measured_span','witness':r,'rounds':rounds}
   basis_insert(B,r)
  if len(B)==before:return {'status':'closed','basis':B,'rounds':rounds}

def chi(x,m):
 r=1
 for i,z in enumerate(x):
  if m>>i&1:r*=z
 return r

def solve_many(A,B):
 # Exact Gauss-Jordan; each row of B contains one or more right-hand sides.
 n=len(A);w=len(B[0]);M=[list(a)+list(b) for a,b in zip(A,B)]
 for j in range(n):
  pivot=next(i for i in range(j,n) if M[i][j])
  M[j],M[pivot]=M[pivot],M[j]
  d=M[j][j];M[j]=[v/d for v in M[j]]
  for i in range(n):
   if i!=j and M[i][j]:
    c=M[i][j];M[i]=[v-c*t for v,t in zip(M[i],M[j])]
 return [r[n:n+w] for r in M]

n=4; X=list(product((-1,1),repeat=n));eta=F(1,5);rho=1-2*eta
# Unknown pairing is positions 1 and 3, task is position 0.
def kernel(x,y):
 a=x[0];b=x[1]*x[3]
 # Nonlinear sign-AND: -1 only when both inputs -1.
 f=F(1+a+b-a*b,2)
 total=F(0)
 for z,w in [(-1,F(2,5)),(1,F(3,5))]:
  R=z*x[2]*a
  pre=(b,R,R*a*x[2],R*f)
  p=w
  for yi,pi in zip(y,pre):p*=1-eta if yi==pi else eta
  total+=p
 return total
K=[[kernel(x,y) for y in X] for x in X]
assert all(sum(r)==1 for r in K)
assert min(map(min,K))>0
# Observed population moments, current design uniform; Gram of Walsh basis I.
# k=4 for this bounded test; general family has a fixed degree bound.
T={}
for S in range(1<<n):
 if S.bit_count()>3:continue
 g=[sum(p*chi(y,S) for p,y in zip(row,X)) for row in K]
 T[S]=clean({R:sum(F(chi(x,R))*gx for x,gx in zip(X,g))/len(X) for R in range(1<<n)})
assert T[1]=={10:rho}  # pairing learned solely from lagged moments
res=discover([{1:F(1)}],T,3)
assert res['status']=='closed';assert set(res['basis'])=={0,1,10,11}
assert len(res['basis'])==4
# Verify true row block probabilities independently on the full test oracle.
q=lambda x:(x[0],x[1]*x[3])
Q=sorted({q(x) for x in X}); rows={}
for x,row in zip(X,K):
 r=tuple(sum(p for y,p in zip(X,row) if q(y)==v) for v in Q)
 if q(x) in rows:assert rows[q(x)]==r
 rows[q(x)]=r
# Core minimality: task alone fails because its next mean is rho*b.
assert T[1].get(10)==rho and rho!=0
# Passive stationary population-readout extension. K and pi are used ONLY in
# oracle generation/validation; the regression learner receives G and H.
N0=len(X)
stationary_A=[[K[i][j]-F(i==j) for i in range(N0)] for j in range(N0-1)]+[[F(1)]*N0]
stationary_b=[[F(0)] for _ in range(N0-1)]+[[F(1)]]
pi=[r[0] for r in solve_many(stationary_A,stationary_b)]
assert sum(pi)==1 and min(pi)>0
assert all(sum(pi[i]*K[i][j] for i in range(N0))==pi[j] for j in range(N0))
assert pi != [F(1,N0)]*N0
old_masks=list(range(N0));next_masks=[S for S in range(N0) if S.bit_count()<=3]
G=[[sum(px*chi(x,R^Q) for x,px in zip(X,pi)) for Q in old_masks] for R in old_masks]
H=[[sum(pi[i]*chi(X[i],R)*sum(K[i][j]*chi(X[j],S) for j in range(N0)) for i in range(N0)) for S in next_masks] for R in old_masks]
def learn_from_moments(G,H,old_masks,next_masks):
 coefficients=solve_many(G,H)
 return {S:clean({R:coefficients[r][s] for r,R in enumerate(old_masks)}) for s,S in enumerate(next_masks)}
T_stationary=learn_from_moments(G,H,old_masks,next_masks)
assert T_stationary==T
stationary_res=discover([{1:F(1)}],T_stationary,3)
assert stationary_res['status']=='closed' and set(stationary_res['basis'])=={0,1,10,11}
stationary_tv=sum(abs(p-F(1,N0)) for p in pi)/2
# With the full n=4 Walsh basis G is orthogonally similar to 16*diag(pi).
stationary_gram_min_eigenvalue=N0*min(pi)

# Crossing obstruction with identical stationary current law and every degree<=1 next moment.
Y=list(product((-1,1),repeat=3));N=len(Y);P=[[F(1,N) for _ in Y] for _ in Y];P2=[r[:] for r in P]
x0=Y.index((-1,-1,-1));x1=Y.index((-1,-1,1));eps=F(1,16)
v=[F(chi(y,3),N) for y in Y]
for j in range(N):P2[x0][j]+=eps*v[j];P2[x1][j]-=eps*v[j]
assert min(map(min,P2))>0
assert all(sum(r)==1 for r in P2)
assert all(sum(P2[i][j] for i in range(N))==1 for j in range(N))
for i in range(N):
 for S in (0,1,2,4):assert sum(P[i][j]*chi(Y[j],S) for j in range(N))==sum(P2[i][j]*chi(Y[j],S) for j in range(N))
# Every old observable has equal one-step mixed moments against measured next features,
# because stationary pi is identical and conditional moments are identical pointwise.
for R in range(N):
 for S in (0,1,2,4):
  assert sum(F(chi(Y[i],R),N)*sum(P[i][j]*chi(Y[j],S) for j in range(N)) for i in range(N))==sum(F(chi(Y[i],R),N)*sum(P2[i][j]*chi(Y[j],S) for j in range(N)) for i in range(N))
block=[j for j,y in enumerate(Y) if y[:2]==(-1,-1)]
gap=sum(P2[x0][j]-P2[x1][j] for j in block);assert gap!=0
exitres=discover([{1:F(1)},{2:F(1)}],{0:{0:F(1)},1:{},2:{},4:{}},1)
assert exitres['status']=='outside_measured_span'
result={'status':'PASS','arithmetic':'exact rational','success':{'raw_states':16,'quotient_states':4,'task_states':2,'discovered_basis_masks':sorted(res['basis']),'unknown_parity_mask':10,'minimum_whole_transition':str(min(map(min,K))),'rounds':res['rounds']},'stationary_success':{'raw_states':16,'quotient_states':4,'population_moments_only_to_learner':True,'stationary_law_nonuniform':True,'stationary_distance_from_uniform_tv':float(stationary_tv),'stationary_min_mass':float(min(pi)),'gram_min_eigenvalue':float(stationary_gram_min_eigenvalue),'operator_recovery_error':'0 exactly','same_discovered_basis':True,'state_preparation_required':False},'crossing':{'raw_states':8,'stationary_law':'uniform, exactly preserved','all_measured_conditional_and_mixed_moments_equal':True,'joint_quotient_row_gap':str(gap),'each_single_bit_quotient_valid':True,'joint_quotient_invalid_in_second_world':True},'symbolic_growth':[{'raw_bits':n,'whole_states':str(2**n),'discovered_core_states':4,'sensor_support':3,'enumerated':False} for n in (8,16,32,64)],'scope':'Growth entries are algebraic counts, not large whole-state runs. Both uniform-design and passive nonuniform stationary population moments recover success; exact stationary data for obstruction. K and pi are oracle-only inputs, not learner inputs. No full-history equivalence claim.'}
out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
