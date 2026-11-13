#!/usr/bin/env python3
"""Derive primitive local factors, eliminate hidden trace variables, compare oracle.
No third-party dependencies. Exact finite-universe possible-realization result.
"""
from itertools import product
from collections import defaultdict
import json

N=6; H=4
OBS=((1,1),(0,0),(1,1),(0,0),(1,1))
TH=tuple(f'm{j}' for j in range(N))
X=lambda t,j:f'x{t}_{j%N}'
class Factor:
 def __init__(self,scope,rows):self.scope=tuple(scope);self.rows=set(map(tuple,rows))
 def join(self,other):
  overlap=tuple(x for x in self.scope if x in other.scope)
  ai=[self.scope.index(x) for x in overlap];bi=[other.scope.index(x) for x in overlap]
  new=tuple(x for x in other.scope if x not in self.scope)
  ni=[other.scope.index(x) for x in new]
  idx=defaultdict(list)
  for row in other.rows:idx[tuple(row[i] for i in bi)].append(row)
  return Factor(self.scope+new,(a+tuple(b[i] for i in ni) for a in self.rows
             for b in idx.get(tuple(a[i] for i in ai),())))
 def project(self,keep):
  scope=tuple(x for x in self.scope if x in keep);ii=[self.scope.index(x) for x in scope]
  return Factor(scope,(tuple(row[i] for i in ii) for row in self.rows))

def build(extra=()):
 fs=[]
 for t in range(H):
  for j in range(N):
   scope=(TH[j],X(t,j-1),X(t,j),X(t,j+1),X(t+1,j))
   rows=[(m,a,b,c,b^(m&a&c)) for m,a,b,c in product((0,1),repeat=4)]
   fs.append(Factor(scope,rows))
 for t,(a,b) in enumerate(OBS):
  fs.append(Factor((X(t,0),X(t,1)),[(q,q^a) for q in (0,1)]))
  fs.append(Factor((X(t,3),X(t,4)),[(q,q^b) for q in (0,1)]))
 return fs+list(extra)

def eliminate(fs,keep):
 peak=0; peak_arity=0; steps=0
 variables=set().union(*(set(f.scope) for f in fs))-set(keep)
 while variables:
  def cost(v):
   bucket=[f for f in fs if v in f.scope]
   union=set().union(*(set(f.scope) for f in bucket))
   return (len(union),sum(len(f.rows) for f in bucket),v)
  v=min(variables,key=cost);bucket=[f for f in fs if v in f.scope]
  fs=[f for f in fs if v not in f.scope]
  bucket.sort(key=lambda f:len(f.rows));joined=bucket[0]
  for f in bucket[1:]:
   joined=joined.join(f);peak=max(peak,len(joined.rows));peak_arity=max(peak_arity,len(joined.scope))
  fs.append(joined.project(set(joined.scope)-{v}));variables.remove(v);steps+=1
 fs.sort(key=lambda f:len(f.rows));joined=Factor((),[()])
 for f in fs:
  joined=joined.join(f);peak=max(peak,len(joined.rows));peak_arity=max(peak_arity,len(joined.scope))
 ii=[joined.scope.index(v) for v in keep]
 return set(tuple(row[i] for i in ii) for row in joined.rows),{'peak_rows':peak,'peak_scope':peak_arity,'eliminated_variables':steps}

def boundary(S,j):return j in S and ((j-1)%N not in S or (j+1)%N not in S)
def cut_factors():
 # p IS UNKNOWN; values choose the third owned coordinate. No requested cut supplied.
 return [Factor(('p',TH[j]),[(p,m) for p in (2,3,4,5) for m in (0,1)
       if not (m and boundary({0,1,p},j))]) for j in range(N)]
def fixed_core(S):
 return [Factor((TH[j],),[(0,)]) for j in range(N) if boundary(S,j)]
def step(x,m):return tuple(x[j]^(m[j]&x[(j-1)%N]&x[(j+1)%N]) for j in range(N))
def obs(x):return(x[0]^x[1],x[3]^x[4])
def fits(m,x):
 for t,y in enumerate(OBS):
  if obs(x)!=y:return False
  if t<H:x=step(x,m)
 return True

keep=TH+tuple(X(0,j) for j in range(N))
data,ds=eliminate(build(),keep)
found,cs=eliminate(build(cut_factors()),('p',)+keep)
joint,js=eliminate(build(fixed_core({0,1,2})+fixed_core({0,1,5})),keep)
V=list(product((0,1),repeat=N))
oracle={m+x for m in V for x in V if fits(m,x)}
assert data==oracle and len(data)==22 and len({row[:N] for row in data})==17
expected={(p,)+m+x for m in V for x in V if fits(m,x) for p in (2,3,4,5)
          if all(not m[j] or not boundary({0,1,p},j) for j in range(N))}
assert found==expected and len(found)==14 and {row[0] for row in found}=={2,5}
assert not joint
# Check autonomous mechanisms over ALL states, not just observed trace states.
# Reuse each persistent mode for all times; the observation fit does not change it.
persistent=0
for row in found:
 p=row[0];m=row[1:1+N];S={0,1,p}
 for x in V:
  nx=step(x,m)
  for j in S:
   if m[j]:
    assert (j-1)%N in S and (j+1)%N in S
    local=x[j]^(x[(j-1)%N]&x[(j+1)%N])
   else:local=x[j]
   assert local==nx[j];persistent+=1
# At least one discovered mechanism has active nonlinear dynamics inside the core.
assert any(row[2]==1 for row in found if row[0]==2) # m1=1; index p,m0,m1
# A shared possible model with two interacting parent cuts under one-bit incoming budget.
m=(1,1,0,1,1,0);x0=(0,1,0,1,0,1)
assert fits(m,x0)
def incoming(S):return {k for j in S if m[j] for k in ((j-1)%N,(j+1)%N) if k not in S}
assert incoming({0,1,2})=={5} and incoming({0,1,5})=={2}
assert incoming({3,4,5})=={2} and incoming({2,3,4})=={5}
# The intersection {0,1} needs both outside bits for all initial states.
outputs=set()
for b2,b5 in product((0,1),repeat=2):
 x=(1,1,b2,0,0,b5);nx=step(x,m);outputs.add((nx[0],nx[1]))
assert len(outputs)==4
out={'status':'PASS','readout_trace':OBS,'data_models_and_initial_states':len(data),
 'distinct_modes':len({row[:N] for row in data}),
 'discovered_task_cores':{str(p):sum(row[0]==p for row in found) for p in (2,3,4,5)},
 'joint_autonomous_witnesses':len(joint),'all_state_local_update_checks':persistent,
 'data_elimination':ds,'discovery_elimination':cs,'joint_elimination':js,
 'primitive_transition_factor_arity':5,'primitive_transition_factor_rows':16,
 'shared_interacting_model':{'modes':m,'initial':x0,'parent_input_bits':1,'intersection_minimum_input_bits':2}}
print(json.dumps(out,indent=2))
