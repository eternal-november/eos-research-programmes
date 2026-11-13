#!/usr/bin/env python3
"""Direct decoder checks for bounded empty-position decorations.
Independent implementation; scalar C4->C2, ranks0..2, at most3 tagged slots.
All nonempty parent supports have nonempty descendant supports. Empty/nullary
positions are retained as typed tuple positions rather than erased.
"""
from itertools import product,combinations_with_replacement
from collections import defaultdict
from pathlib import Path
from hashlib import sha256
import json

def require(v,m):
 if not v:raise RuntimeError(m)

def main():
 types=tuple(p for length in range(4) for p in product(range(3),repeat=length) if sum(p)<=2)
 carriers={p:tuple(product(range(4),repeat=sum(v>0 for v in p))) for p in types}
 obs={p:tuple(x if sum(v>0 for v in p)==1 else tuple(y%2 for y in x) for x in carriers[p]) for p in types}
 ix={p:{x:i for i,x in enumerate(carriers[p])} for p in types}
 rows=[]
 for source in types:
  for slots in range(4):
   if slots==0:
    if source:continue
    boundaries=[(0,)]
   else:boundaries=[(0,)+mid+(len(source),) for mid in combinations_with_replacement(range(len(source)+1),slots-1)]
   for limits in boundaries:
    children=tuple(source[a:b] for a,b in zip(limits,limits[1:]))
    outer=tuple(sum(child) for child in children);ins=(outer,)+children
    concrete=[set() for _ in carriers[source]];q_graft={};records=0
    for values in product(*(range(len(carriers[p])) for p in ins)):
     parent=iter(carriers[outer][values[0]]);result=[]
     for child,childid in zip(children,values[1:]):
      bs=carriers[child][childid]
      if sum(child)>0:
       a=next(parent);result.extend((a+b)%4 for b in bs)
      else:require(not bs,'empty child has coefficients')
     require(next(parent,None) is None,'unconsumed parent')
     x=ix[source][tuple(result)];fo=tuple(obs[p][v] for p,v in zip(ins,values));so=obs[source][x]
     concrete[x].add(fo)
     if fo in q_graft:require(q_graft[fo]==so,'graft representative dependence')
     else:q_graft[fo]=so
     records+=1
    q_cut=defaultdict(set)
    for f,s in q_graft.items():q_cut[s].add(f)
    for x,s in enumerate(obs[source]):require(concrete[x]==q_cut[s],'concrete versus quotient joint-cut decoder')
    rows.append({'source':source,'outer':outer,'children':children,'records':records})
 # Full units only at an actual old identity: coefficient exact at rank1;
 # rank0 has one coefficient assignment, so any exact old unit guard is uniform.
 for p in types:
  if sum(v>0 for v in p)==1:
   require(all((x==(0,))==(y==(0,)) for x,y in product(carriers[p],repeat=2) if obs[p][ix[p][x]]==obs[p][ix[p][y]]),'rank1 unit gate')
 result={'status':'Tagged empty-position decoder checks passed','group':'C4 to C2','maximum_tagged_slots':3,
         'maximum_active_vertex_sum':2,'type_count':len(types),'operation_count':len(rows),
         'full_record_count':sum(x['records'] for x in rows),'operations':rows,
         'scope':'Finite tagged size profiles only; not all old graphs, unbounded empty strings, or unbounded trees',
         'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
 out=Path(__file__).with_name('rank_sensitive_empty_results.json');out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('operations','checker_sha256')},indent=2))
if __name__=='__main__':main()
