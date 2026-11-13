#!/usr/bin/env python3
"""Independent audit of saved finite-test certificate; no simulator imports."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
import json,math
P=Path(__file__).resolve().parents[1]/'examples'
h=json.loads((P/'monitor_service_holdout_histograms.json').read_text())
q=json.loads((P/'monitor_service_exact_predictions.json').read_text())
c=json.loads((P/'monitor_service_frozen_candidate.json').read_text())
n=50000;r=F(231,10000);nr=0;worst=F(0)
for a,b in zip(h,q):
 assert a['policy']==b['policy']
 assert len(a['histograms'])==84
 assert [tuple(x[0]) for x in a['histograms']]==[tuple(c for t in times for c in (2*t,2*t+1)) for times in combinations(range(9),3)]
 for (coords,hist),(coords2,nums,den) in zip(a['histograms'],b['probabilities']):
  assert coords==coords2 and sum(hist)==n and sum(nums)==den
  assert all(x>=0 for x in hist+nums) and den>0
  tv=sum(abs(F(x,n)-F(y,den)) for x,y in zip(hist,nums))/2
  worst=max(worst,tv);nr+=1
# Entire union bound using exact exponential lower bound.
x=2*n*r*r
lower=sum((x**k/F(math.factorial(k)) for k in range(100)),F(0))
fail=F(4*(84*(2**64-2)+4*(2**10-2)))/lower
assert fail<F(1,20) and worst+r<F(1,20)
# Independent DP using Fraction vectors. Each triple bit is accumulated from
# observation-time labels, not simulator bit positions or integer denominator DP.
masks=c['masks'];local=[[F(s) for s in row] for row in c['local']];mix=F(c['shared_weight']);nu=[F(s) for s in c['initial']]
pairs=list(product([0,1],repeat=2))
def action(name,old,now):
 if name=='clear':return tuple(1-v for v in now)
 if name=='busy':return now
 if name=='crossed':return(now[1],1-now[0])
 if name=='remembered_change':return tuple(a^b for a,b in zip(old,now))
 raise AssertionError(name)
def step(name,old,now):
 values=now+old+action(name,old,now);pp=[]
 for mask,row in zip(masks,local):
  idx=0
  for j in mask:idx=2*idx+values[j]
  pp.append(row[idx])
 p,z=pp;joint=(1-mix)*p*z+mix*min(p,z)
 return {(0,0):1-p-z+joint,(0,1):z-joint,(1,0):p-joint,(1,1):joint}
def calculate(name,coords):
 selected={coord:(i,coord//2,coord%2) for i,coord in enumerate(coords)}
 def observe(word,now,t):
  word=list(word)
  for _,(i,tt,port) in selected.items():
   if tt==t:word[i]=now[port]
  return tuple(word)
 current={}
 for mass,(old,now) in zip(nu,product(pairs,repeat=2)):
  current[(old,now,observe(tuple([-1]*len(coords)),now,0))]=mass
 for t in range(1,max(coords)//2+1):
  nxt={}
  for (old,now,word),mass in current.items():
   for out,prob in step(name,old,now).items():
    k=(now,out,observe(word,out,t));nxt[k]=nxt.get(k,F(0))+mass*prob
  current=nxt
 result=[F(0)]*(2**len(coords))
 for (_,_,word),mass in current.items():
  assert -1 not in word
  idx=sum(v*2**(len(word)-1-i) for i,v in enumerate(word));result[idx]+=mass
 return result
checks=0
for block in q:
 for j in [0,20,41,62,83]:
  coords,nums,den=block['probabilities'][j]
  actual=calculate(block['policy'],coords)
  assert actual==[F(a,den) for a in nums];checks+=1
# Recompute every recorded histogram from saved complete episodes.
import numpy as np
mon=json.loads((P/'monitor_service_monitor_results.json').read_text())
rawchecks=0;monitorchecks=0
for block,mblock in zip(h,mon):
 name=block['policy'];records=np.load(P/('monitor_service_holdout_'+name+'.npz'))
 states=records['readouts'];flat=states[:,1:].reshape(n,-1)
 assert states.shape==(n,10,2)
 for coords,hist in block['histograms']:
  values=sum(flat[:,c]*2**(len(coords)-1-k) for k,c in enumerate(coords))
  assert np.bincount(values,minlength=64).tolist()==hist;rawchecks+=1
 for row in mblock['max_run_monitors']:
  symbol=tuple(row['symbol']);run=np.zeros(n,dtype=int);maximum=np.zeros(n,dtype=int)
  for t in range(1,10):
   run=np.where(np.all(states[:,t]==symbol,axis=1),run+1,0);maximum=np.maximum(maximum,run)
  assert np.bincount(maximum,minlength=10).tolist()==row['counts'];rawchecks+=1
  # Independent rational product-state computation for maximum-run distribution.
  cur={}
  for mass,(old,now) in zip(nu,product(pairs,repeat=2)):
   v=int(now==symbol);cur[(old,now,v,v)]=mass
  for t in range(8):
   nxt={}
   for (old,now,run,mx),mass in cur.items():
    for out,prob in step(name,old,now).items():
     rr=run+1 if out==symbol else 0;k=(now,out,rr,max(mx,rr))
     nxt[k]=nxt.get(k,F(0))+mass*prob
   cur=nxt
  law=[F(0)]*10
  for (_,_,_,mx),mass in cur.items():law[mx]+=mass
  assert law==[F(x,row['prediction_denominator']) for x in row['prediction_numerators']]
  fit=sum(abs(F(x,n)-y) for x,y in zip(row['counts'],law))/2
  assert fit==F(row['TV_fit']);worst=max(worst,fit);monitorchecks+=1
assert worst+r<F(1,20)
print(json.dumps({'status':'PASS','projection_certificates':nr,'independent_exact_projection_DP_checks':checks,'independent_exact_maxrun_DP_checks':monitorchecks,'raw_histogram_checks':rawchecks,'uniform_bound':str(worst+r),'uniform_bound_float':float(worst+r),'confidence_failure_bound_float':float(fail)},indent=2))
