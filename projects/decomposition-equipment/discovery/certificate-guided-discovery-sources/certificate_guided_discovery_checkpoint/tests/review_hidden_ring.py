#!/usr/bin/env python3
"""Independent exhaustive controls for nonlinear hidden ring example."""
from itertools import product
import json

def step(x,theta):
 n=len(x)
 return tuple(x[j]^(theta[j]&x[(j-1)%n]&x[(j+1)%n]) for j in range(n))
def select(x,S):return tuple(x[j] for j in sorted(S))
def closure(S,theta):
 n=len(theta)
 return all(theta[j]==0 or {(j-1)%n,(j+1)%n}<=S for j in S)
autonomy_checks=0
for n in range(3,7):
 states=tuple(product((0,1),repeat=n))
 subsets=[{j for j in range(n) if mask>>j&1} for mask in range(1<<n)]
 for theta in states:
  nxt={x:step(x,theta) for x in states}
  for S in subsets:
   outputs={};actual=True
   for x in states:
    a,b=select(x,S),select(nxt[x],S)
    if a in outputs and outputs[a]!=b:actual=False;break
    outputs[a]=b
   assert actual==closure(S,theta)
   autonomy_checks+=1
n=6;states=tuple(product((0,1),repeat=n))
readouts=((1,1),(0,0),(1,1),(0,0),(1,1))
possible=[]
for theta in states:
 for initial in states:
  x=initial;obs=[]
  for t in range(5):
   obs.append((x[0]^x[1],x[3]^x[4]));x=step(x,theta)
  if tuple(obs)==readouts:possible.append((theta,initial))
assert len(possible)==22 and len({theta for theta,x in possible})==17
cores={p:[w for w in possible if closure({0,1,p},w[0])] for p in (2,3,4,5)}
assert {p:len(ws) for p,ws in cores.items()}=={2:7,3:0,4:0,5:7}
assert not set(cores[2])&set(cores[5])
assert len(set(possible)-set(cores[2])-set(cores[5]))==8
# If both candidate triples autonomous, changing task parity is impossible.
for theta in states:
 if closure({0,1,2},theta) and closure({0,1,5},theta):
  assert theta[0]==theta[1]==0
  for x in states:
   y=step(x,theta)
   assert x[0]^x[1]==y[0]^y[1]
# Independent four-output boundary lower bound at fixed local state.
theta=(1,1,0,1,1,0)
outputs={select(step((1,1,x2,0,0,x5),theta),{0,1}) for x2,x5 in product((0,1),repeat=2)}
assert len(outputs)==4
# Original ordered graph profiles are NOT equal for these ring triples.
edges={tuple(sorted((j,(j+1)%6))) for j in range(6)}
def induced(V):return {(a,b) for a in range(len(V)) for b in range(a+1,len(V)) if (V[a],V[b]) in edges}
assert induced((0,1,2))=={(0,1),(1,2)}
assert induced((0,1,5))=={(0,1),(0,2)}
assert induced((0,1,2))!=induced((0,1,5))
print(json.dumps({'status':'PASS','autonomy_iff_closure_cases':autonomy_checks,
 'data_consistent_world_initial_pairs':len(possible),'mode_count':17,
 'autonomous_core_witnesses':{str(p):len(ws) for p,ws in cores.items()},
 'data_pairs_without_requested_core':8,'joint_autonomous_pairs':0,
 'intersection_output_distinctions':4,'ordered_ring_profile_mismatch_verified':True},indent=2))
