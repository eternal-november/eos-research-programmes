#!/usr/bin/env python3
"""Exact population-table discovery calibration, NOT a finite-data experiment."""
from fractions import Fraction as F
from itertools import product, combinations
import json, math
BITS=list(product((0,1), repeat=6))
# Global context: own/current y0,y1; prior z0,z1; actions a0,a1.
def probs(c):
 y0,y1,z0,z1,a0,a1=c
 return (F(1+3*a0+2*z0+2*y1,10),F(1+3*a1+2*z1+2*y0,10))
def kernel(c):
 p,q=probs(c); pq=(p*q+min(p,q))/2
 return (1-p-q+pq,q-pq,p-pq,pq)
def tv(p,q): return sum(abs(x-y) for x,y in zip(p,q))/2
# These are supplied evidence tables, not a supplied latent model in the search.
TABLE={c:kernel(c) for c in BITS}
assert all(sum(k)==1 and min(k)>0 for k in TABLE.values())
def marginal(c,i):
 k=TABLE[c]; return k[2]+k[3] if i==0 else k[1]+k[3]
def feasible_masks(i):
 out=[]
 for n in range(7):
  for mask in combinations(range(6),n):
   by={};good=True
   for c in BITS:
    key=tuple(c[j] for j in mask);p=marginal(c,i)
    if key in by and by[key]!=p: good=False;break
    by[key]=p
   if good: out.append(mask)
 return out
masks=[feasible_masks(i) for i in (0,1)]
assert masks[0][0]==(1,2,4) and masks[1][0]==(0,3,5)
assert len([m for m in masks[0] if len(m)==3])==1
assert len([m for m in masks[1] if len(m)==3])==1
# Derive mixture weight from table instead of inserting it into discovery.
lambdas=set()
for c in BITS:
 p,q=probs(c); lambdas.add((TABLE[c][3]-p*q)/(min(p,q)-p*q))
assert lambdas=={F(1,2)}
# Positive context-independent shared response witness, 10 common atoms and100 independent atoms.
for c in BITS:
 p,q=probs(c); out=[F(0)]*4
 for u in range(10):
  b0=int(F(u,10)<p);b1=int(F(u,10)<q);out[2*b0+b1]+=F(1,20)
 for u,v in product(range(10),repeat=2):
  b0=int(F(u,10)<p);b1=int(F(v,10)<q);out[2*b0+b1]+=F(1,200)
 assert tuple(out)==TABLE[c]
# A no-memory or no-neighbor context merges histories whose marginal next laws differ .2.
separations={}
for i,relevant in enumerate([(1,2,4),(0,3,5)]):
 for missing in relevant:
  best=F(0)
  for c in BITS:
   d=list(c);d[missing]=1-d[missing];d=tuple(d)
   best=max(best,abs(marginal(c,i)-marginal(d,i)))
  separations[f'port{i}_omit_coordinate{missing}']=str(best)
assert set(separations.values())=={'1/5','3/10'}
# Joint independence gives wrong predictions even with exact marginal summaries.
max_product_error=max(tv(TABLE[c],((1-probs(c)[0])*(1-probs(c)[1]),
 (1-probs(c)[0])*probs(c)[1],probs(c)[0]*(1-probs(c)[1]),probs(c)[0]*probs(c)[1])) for c in BITS)
# HMM continuum calibration: distinct rational posterior updates after all-1 histories.
p=F(1,2);seen=set()
for _ in range(50):
 r=F(1,10)+F(4,5)*p;nxt=4*r/(1+3*r)
 assert nxt>p and nxt not in seen;seen.add(nxt);p=nxt
# Same-time lower bound: t+1 ordered 0...01...1 histories.
for t in range(1,21):
 vals=[]
 for k in range(t+1):
  p=F(1,2)
  for y in [0]*(t-k)+[1]*k:
   r=F(1,10)+F(4,5)*p
   p=4*r/(1+3*r) if y else r/(4-3*r)
  vals.append(p)
 assert all(x<y for x,y in zip(vals,vals[1:]))
report={'status':'PASS','joint_contexts':64,'local_masks_per_port':64,
 'minimal_masks':[[1,2,4],[0,3,5]],'positive_shared_response_atoms':110,
 'recovered_common_mixture_weight':'1/2','max_product_predictor_one_step_TV':str(max_product_error),
 'omitted_feature_marginal_separations':separations,
 'hmm_distinct_all_one_predictive_states_checked':50,
 'data_status':'Exact population-table synthetic calibration, not sampled evidence or latent architecture identification'}
print(json.dumps(report,indent=2))
