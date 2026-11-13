#!/usr/bin/env python3
"""Independent histogram proposal reconstruction and generic-LP DP check."""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
from math import isqrt,factorial
import json
import numpy as np
from scipy.optimize import linprog
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'examples/weighted_sampled_service_histogram.json').read_text())
ref=json.loads((ROOT/'examples/weighted_episode_discovery_checks.json').read_text())
N=data['N']; pairs=list(product((0,1),repeat=2))
counts=defaultdict(lambda:[0]*4); initials=defaultdict(int)
for z,y,a,u,b,v,n in data['episodes']:
 z,y,a,u,b,v=map(tuple,(z,y,a,u,b,v))
 initials[z,y]+=n;counts[0,(z,y),a][pairs.index(u)]+=n;counts[1,(z,y,a,u),b][pairs.index(v)]+=n
assert sum(initials.values())==N==10240000 and len(counts)==1088
laws={k:tuple(F(x,sum(v)) for x in v) for k,v in counts.items()}
port_tables=[];masks=[]
for i in (0,1):
 good=[]
 for maskbits in range(64):
  seen=defaultdict(list)
  for (t,h,a),row in laws.items():
   if t:continue
   z,y=h;c=y+z+a;key=tuple(c[j] for j in range(6) if maskbits>>j&1)
   seen[key].append(sum(row[k] for k,o in enumerate(pairs) if o[i]))
  if all(max(v)-min(v)<=F(1,100) for v in seen.values()):good.append(maskbits)
 minimal=[m for m in good if not any(k!=m and k&m==k for k in good)]
 assert minimal==([22] if i==0 else [41]);mask=minimal[0];masks.append(mask)
 accum=defaultdict(lambda:[0,0])
 for (t,h,a),row in counts.items():
  if t:continue
  z,y=h;c=y+z+a;key=tuple(c[j] for j in range(6) if mask>>j&1)
  accum[key][0]+=sum(row[k] for k,o in enumerate(pairs) if o[i]);accum[key][1]+=sum(row)
 port_tables.append({k:F(round(10*F(v[0],v[1])),10) for k,v in accum.items()})
def predictor(h,a,t):
 z,y=h if t==0 else (h[1],h[3]);c=y+z+a
 p,q=[port_tables[i][tuple(c[j] for j in range(6) if masks[i]>>j&1)] for i in (0,1)]
 b=(p*q+min(p,q))/2
 return (1-p-q+b,q-b,p-b,b)
def radius(n,T):
 k=isqrt((T*10**12)//(2*n))
 while 2*n*k*k<T*10**12:k+=1
 r=min(F(1),F(k,10**6));assert r==1 or 2*n*r*r>=T
 return r
def tv(p,q):return sum(abs(x-y) for x,y in zip(p,q))/2
radii={key:radius(sum(v),13) for key,v in counts.items()}
gamma={key:min(F(1),tv(p,predictor(key[1],key[2],key[0]))+radii[key]) for key,p in laws.items()}
assert all(tv(p,predictor(key[1],key[2],key[0]))<=radii[key] for key,p in laws.items())
lp_calls=0
def maximum(emp,r,values):
 global lp_calls
 m=len(emp);eye=np.eye(m)
 A=np.vstack([np.hstack([eye,-eye]),np.hstack([-eye,-eye]),np.r_[np.zeros(m),np.ones(m)][None,:]])
 B=np.r_[list(map(float,emp)),-np.array(list(map(float,emp))),2*float(r)]
 result=linprog(np.r_[-np.array(list(map(float,values))),np.zeros(m)],A_ub=A,b_ub=B,A_eq=np.r_[np.ones(m),np.zeros(m)][None,:],b_eq=[1.],bounds=[(0,None)]*(2*m),method='highs')
 assert result.success;lp_calls+=1
 return -result.fun
last={}
for (t,h,a),g in gamma.items():
 if t:last[h]=max(last.get(h,0),g)
first={}
for h in initials:
 first[h]=max(float(gamma[0,h,a])+maximum(laws[0,h,a],radii[0,h,a],[last[h+(a,o)] for o in pairs]) for a in pairs)
keys=list(initials);empinit=[F(initials[k],N) for k in keys];ri=radius(N,16)
initialgap=ri+tv(empinit,[F(1,16)]*16)
result=float(initialgap)+maximum(empinit,ri,[first[k] for k in keys])
assert abs(result-float(F(ref['weighted_exact_rational'])))<1e-10
failure=F(14*1088)/sum(F(13)**k/factorial(k) for k in range(101))+F(65534)/sum(F(16)**k/factorial(k) for k in range(101))
assert failure==F(ref['confidence_failure_bound_exact']) and failure<F(1,20)
assert F(ref['weighted_exact_rational'])<=F(ref['outward_rounded_bound'])<F(1,20)
assert ref['acceptance_threshold']=='1/20'
print(json.dumps({'status':'PASS','independent_LP_expectation_checks':lp_calls,'rows':len(counts),'data_recovered_masks':masks,'independent_weighted_J_upper':result,'fixed_unconditional_confidence_bound':float(failure),'scope':'Independent numerical LP corroboration plus exact radius/confidence arithmetic; synthetic finite H=2 only'},indent=2))
