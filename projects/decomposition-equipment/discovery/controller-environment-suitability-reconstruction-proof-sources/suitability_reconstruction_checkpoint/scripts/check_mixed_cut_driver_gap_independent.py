#!/usr/bin/env python3
"""Independent partial-task cut coloring and causal update-table search."""
from itertools import product,combinations
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[1]
TASK={'0000':0,'0001':1,'0010':0,'0110':1,'0111':0,'1000':0,'1001':1,'1011':0,'1100':1}
WORDS=tuple(sorted(TASK))
def canon(values):
 d={};return tuple(d.setdefault(v,len(d)) for v in values)
def edges(t):
 ps=sorted({w[:t] for w in WORDS});out=set()
 for a,b in combinations(ps,2):
  if any(a+s in TASK and b+s in TASK and TASK[a+s]!=TASK[b+s] for s in map(''.join,product('01',repeat=4-t))):out.add((a,b))
 return ps,out
def chromatic(t):
 ps,es=edges(t)
 for b in range(1,len(ps)+1):
  for vals in product(range(b),repeat=len(ps)):
   col=dict(zip(ps,vals))
   if all(col[a]!=col[z] for a,z in es):return b,col
 raise AssertionError

def solve(b,profile=None):
 # Each layer stores actual memory state for each possible complete input.
 # A transition table has access only to oldmemory and the next received bit.
 first=tuple(0 for _ in WORDS)
 layers=[{first:None}]; witness=[]
 for t in range(4):
  new={}
  for prev in layers[-1]:
   ks=sorted({(prev[i],w[t]) for i,w in enumerate(WORDS)})
   for vals in product(range(profile[t+1] if profile else b),repeat=len(ks)):
    table=dict(zip(ks,vals));nxt=canon(table[prev[i],w[t]] for i,w in enumerate(WORDS))
    if nxt not in new:new[nxt]=prev
  layers.append(new)
 final=None
 for enc in layers[-1]:
  outputs={}
  for state,w in zip(enc,WORDS):outputs.setdefault(state,set()).add(TASK[w])
  if all(len(s)==1 for s in outputs.values()):final=enc;break
 if final is not None:
  path=[final]
  for t in range(4,0,-1):path.append(layers[t][path[-1]])
  path.reverse()
  # Independently derive actual update tables and check all words.
  tables=[]
  for t in range(4):
   table={}
   for i,w in enumerate(WORDS):
    key=(path[t][i],w[t]);out=path[t+1][i]
    assert key not in table or table[key]==out
    table[key]=out
   tables.append(table)
  output={path[-1][i]:TASK[w] for i,w in enumerate(WORDS)}
  for w in WORDS:
   m=0
   for t,ch in enumerate(w):m=tables[t][m,ch]
   assert output[m]==TASK[w]
  witness={'cut_encodings':[{w[:t]:path[t][i] for i,w in enumerate(WORDS)} for t in range(5)],'updates':[{str(k):v for k,v in tab.items()} for tab in tables],'output':output,'width_profile':[len(set(x)) for x in path]}
 return {'exists':final is not None,'reachable_encoding_counts':[len(x) for x in layers],'witness':witness or None}
def main():
 local=[chromatic(t) for t in range(5)]
 assert [x[0] for x in local]==[1,1,2,2,2]
 two=solve(2);three=solve(3)
 assert not two['exists'] and three['exists']
 assert three['witness']['width_profile']==[1,1,2,3,2]
 alternative=solve(3,[1,2,3,2,2]);meet=solve(2,[1,1,2,2,2])
 assert alternative['exists'] and not meet['exists']
 # Exhaust resource profiles around both Pareto minima. The theorem beyond
 # these finite cases is the direct argument in the audit.
 frontier_cases=0
 A=[1,2,3,2,2];B=[1,1,2,3,2]
 for b1,b2,b3,b4 in product(range(1,3),range(1,4),range(1,4),range(1,3)):
  p=[1,b1,b2,b3,b4]
  predicted=any(all(x<=y for x,y in zip(m,p)) for m in (A,B))
  assert solve(max(p),p)['exists']==predicted
  frontier_cases+=1
 # Exact local path forcing contradiction in every 2-coloring.
 _,e2=edges(2);_,e3=edges(3)
 path2=['01','00','11','10'];path3=['001','011','000','101']
 for path,es in [(path2,e2),(path3,e3)]:
  assert all(tuple(sorted((a,b))) in es for a,b in zip(path,path[1:]))
 # path2 has3edges, so01!=10,00=10; shared observed nextbit1 updates
 # 00->001 and10->101 must coincide. path3 has3edges and forces unequal.
 for vals in product(range(2),repeat=4):
  c=dict(zip(sorted({w[:2] for w in WORDS}),vals))
  if all(c[a]!=c[b] for a,b in e2):assert c['00']==c['10']
 # Every graph-colorability localcheck passes but table-coherencecheck rejects.
 rep={'status':'PASS','task':TASK,'local_chromatic_numbers':[x[0] for x in local],'pareto_frontier':[A,B],'independent_resource_profile_cases':frontier_cases,'local_colorings':[x[1] for x in local], 'two_state_causal_search':two,'alternative_early_repair':alternative,'infeasible_profile_meet':meet,'three_state_causal_search':three,'cut2_edges':sorted(e2),'cut3_edges':sorted(e3),'contradiction_paths':[path2,path3],'negative_control':'Independent per-cut colorability falsely accepts2states; physical update-table search rejects it.','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 out=ROOT/'review/Mixed_Cut_Driver_Gap_Independent_Results.json';out.write_text(json.dumps(rep,indent=2)+'\n');print(json.dumps(rep,indent=2))
if __name__=='__main__':main()
