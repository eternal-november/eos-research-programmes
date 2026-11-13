#!/usr/bin/env python3
"""Independent audit of saved finite-test certificate; no simulator imports."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
import json,math
P=Path(__file__).resolve().parents[1]/'examples'
h=json.loads((P/'sparse_service_holdout_histograms.json').read_text())
q=json.loads((P/'sparse_service_exact_predictions.json').read_text())
c=json.loads((P/'sparse_service_frozen_candidate.json').read_text())
n=20000;r=F(41,2000);nr=0;worst=F(0)
for a,b in zip(h,q):
 assert a['policy']==b['policy']
 assert len(a['histograms'])==816
 assert [tuple(x[0]) for x in a['histograms']]==list(combinations(range(18),3))
 for (coords,hist),(coords2,nums,den) in zip(a['histograms'],b['probabilities']):
  assert coords==coords2 and sum(hist)==n and sum(nums)==den
  assert all(x>=0 for x in hist+nums) and den>0
  tv=sum(abs(F(x,n)-F(y,den)) for x,y in zip(hist,nums))/2
  worst=max(worst,tv);nr+=1
# Entire union bound using exact exponential lower bound.
x=2*n*r*r
lower=sum((x**k/F(math.factorial(k)) for k in range(100)),F(0))
fail=F(nr*254)/lower
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
  current[(old,now,observe((-1,-1,-1),now,0))]=mass
 for t in range(1,max(coords)//2+1):
  nxt={}
  for (old,now,word),mass in current.items():
   for out,prob in step(name,old,now).items():
    k=(now,out,observe(word,out,t));nxt[k]=nxt.get(k,F(0))+mass*prob
  current=nxt
 result=[F(0)]*8
 for (_,_,word),mass in current.items():
  assert -1 not in word
  idx=4*word[0]+2*word[1]+word[2];result[idx]+=mass
 return result
checks=0
for block in q:
 for j in [0,41,207,511,815]:
  coords,nums,den=block['probabilities'][j]
  actual=calculate(block['policy'],coords)
  assert actual==[F(a,den) for a in nums];checks+=1
print(json.dumps({'status':'PASS','projection_certificates':nr,'independent_exact_DP_checks':checks,'uniform_bound':str(worst+r),'uniform_bound_float':float(worst+r),'confidence_failure_bound_float':float(fail)},indent=2))
