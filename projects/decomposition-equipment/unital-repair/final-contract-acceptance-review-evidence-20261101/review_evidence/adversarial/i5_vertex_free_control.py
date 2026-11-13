"""Conditional diagnostic ONLY: adds vertex-free identity-cut feasibility.
Does not assert the disputed I5 permitted grammar contains that cut.
"""
from itertools import product
from pathlib import Path
import json,hashlib
if not __debug__: raise RuntimeError('Optimized execution disallowed')
def comp(a,b):return tuple(a[i] for i in b)
def canon(keys):
 d={};return tuple(d.setdefault(k,len(d)) for k in keys)
def closure(k):
 e=tuple(range(k));a=(k-1,1,1)+tuple(range(2,k-1));b=(1,2)+(1,)*(k-2)
 S={e};todo=[e]
 while todo:
  x=todo.pop()
  for g in (a,b):
   y=comp(g,x)
   if y not in S:S.add(y);todo.append(y)
 return e,a,b,sorted(S)
def repair(M,e,start,unit):
 idx={x:i for i,x in enumerate(M)};table=[[idx[comp(x,y)] for y in M] for x in M]
 P=canon(start); stages=[len(set(P))]; hist=[P]
 while True:
  sig=[set() for x in M]
  for i,j in product(range(len(M)),repeat=2):sig[table[i][j]].add((P[i],P[j]))
  Q=canon([(P[i],frozenset(sig[i]), x==e if unit else None) for i,x in enumerate(M)])
  if Q==P:return stages,P,hist
  P=Q;stages.append(len(set(P)));hist.append(P)
rows=[]
for k in range(4,11):
 e,a,b,M=closure(k);H={e,b,comp(b,b)};I={x:i for i,x in enumerate(M)}
 old,P,_=repair(M,e,[x in H for x in M],False)
 new,Q,hist=repair(M,e,[x in H for x in M],True)
 top,R,_=repair(M,e,[True]*len(M),True)
 assert P[I[e]]==P[I[b]] and Q[I[e]]!=Q[I[b]]
 assert len(set(R))>1
 rows.append({'k':k,'size':len(M),'binary_only_counts':old,'binary_plus_vertex_free_counts':new,'binary_plus_vertex_free_top_counts':top,'old_e_equals_b':True,'new_e_equals_b':False,'final_new_partition':[[M[i] for i,p in enumerate(Q) if p==c] for c in sorted(set(Q))]})
r={'status':'conditional counterexample confirmed','condition':'Only if the permitted cut doctrine includes the vertex-free tree with feasibility precisely at the identity.','rows':rows,'implications':['Every-old-cut lifting fails for enriched (old identity,l != identity).','C-only index partition h is not stable in identity old record.','Original binary-only exact round/count formula no longer describes this enlarged splitter.','C(top)=top fails; channel-product nonempty-fibre hypothesis fails on the omitted nonidentity coordinate.','Discrete simultaneous optimum lower bound survives extra cut tests; non-discrete group quotient control fails if it identifies identity with another group element.'],'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('i5_vertex_free_control_results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({**r,'rows':[{k:v for k,v in x.items() if k!='final_new_partition'} for x in rows]},indent=2))
