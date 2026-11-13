#!/usr/bin/env python3
"""Independent checks with literal old records, not unit masks by active size.
The finite catalogue is a named subdiagram of terminal-grade edgeless graph
operations. It is not closed under arbitrary empty insertion, nor claimed to be
an enumeration of all old records. Units are derived from the full old record.
"""
from dataclasses import dataclass,asdict
from itertools import product
from collections import defaultdict
from pathlib import Path
from hashlib import sha256
import json

class Failure(RuntimeError):pass
def check(v,m):
 if not v:raise Failure(m)
def canon(keys):
 d={};return tuple(d.setdefault(x,len(d)) for x in keys)

@dataclass(frozen=True)
class OldRecord:
 vertices:tuple
 ordered_inputs:tuple
 edges:tuple=()
 grade_arrow:str='terminal_identity'
 old_scalar:int=1
 def rank(self):return sum(bool(x) for x in self.ordered_inputs)
 def is_identity(self):
  return self.ordered_inputs==(self.vertices,) and self.grade_arrow=='terminal_identity' and self.old_scalar==1

RECORDS=(('empty_nullary',OldRecord((),())),
         ('empty_identity',OldRecord((),((),))),
         ('identity_vertex0',OldRecord((0,),((0,),))),
         ('identity_vertex1',OldRecord((1,),((1,),))),
         ('identity_graph01',OldRecord((0,1),((0,1),))),
         ('ordered_two_branch',OldRecord((0,1),((0,),(1,)))),
         ('one_active_then_empty',OldRecord((0,1),((0,1),()))),
         ('two_branch_with_middle_empty',OldRecord((0,1),((0,),(),(1,)))))

def operations():
 recs=[r for _,r in RECORDS];ix={r:i for i,r in enumerate(recs)};ops=[]
 for outer,r in enumerate(recs):
  for children in product(*(tuple(i for i,s in enumerate(recs) if s.vertices==part) for part in r.ordered_inputs)):
   parts=tuple(p for child in children for p in recs[child].ordered_inputs)
   result=OldRecord(r.vertices,parts)
   if result in ix:ops.append((ix[result],outer,children))
 return ops

def table_for_M4():
 identity=(0,1,2,3);a=(3,1,1,2);b=(1,2,1,1)
 comp=lambda x,y:tuple(x[z] for z in y)
 todo=[identity];seen={identity}
 while todo:
  x=todo.pop()
  for y in (a,b):
   z=comp(x,y)
   if z not in seen:seen.add(z);todo.append(z)
 xs=tuple(sorted(seen));ix={x:i for i,x in enumerate(xs)}
 m=tuple(tuple(ix[comp(x,y)] for y in xs) for x in xs)
 H={ix[identity],ix[b],ix[comp(b,b)]}
 return m,ix[identity],tuple(x in H for x in range(len(xs)))

def build_records(m):
 n=len(m);carriers=[tuple(product(range(n),repeat=r.rank())) for _,r in RECORDS]
 indexes=[{x:i for i,x in enumerate(c)} for c in carriers];rows=[]
 for source,outer,children in operations():
  sorts=(outer,)+children;records=[]
  for values in product(*(range(len(carriers[s])) for s in sorts)):
   parents=iter(carriers[outer][values[0]]);result=[]
   for child,childvalue in zip(children,values[1:]):
    bs=carriers[child][childvalue]
    if RECORDS[child][1].vertices:
     aa=next(parents);result.extend(m[aa][bb] for bb in bs)
    else:check(not bs,'empty coefficient')
   check(next(parents,None) is None,'unconsumed parent')
   records.append((indexes[source][tuple(result)],values))
  rows.append((source,sorts,records))
 return carriers,rows

def unit_mask(carriers,unit):
 return [tuple(r.is_identity() and all(v==unit for v in xs) for xs in C) for (_,r),C in zip(RECORDS,carriers)]

def refinement(m,unit,scalar_seed,contexts,transport=None,expected=None):
 carriers,rows=build_records(m);units=unit_mask(carriers,unit)
 p=tuple(canon(tuple(scalar_seed[x] for x in xs) for xs in C) for C in carriers)
 hist=[[len(set(z)) for z in p]]
 while True:
  keys=[[[p[s][x],units[s][x]] for x in range(len(C))] for s,C in enumerate(carriers)]
  if transport is not None:
   for sort,C in enumerate(carriers):
    cx={xs:i for i,xs in enumerate(C)}
    for x,xs in enumerate(C):keys[sort][x].append(p[sort][cx[tuple(transport[v] for v in xs)]])
  for source,sorts,records in rows:
   sig=[set() for _ in carriers[source]]
   for x,vals in records:sig[x].add(tuple(p[s][v] for s,v in zip(sorts,vals)))
   for x,z in enumerate(sig):keys[source][x].append(frozenset(z))
   if contexts:
    for pos,sort in enumerate(sorts):
     cs={}
     for x,vals in records:
      other=vals[:pos]+vals[pos+1:]
      if other not in cs:cs[other]=[None]*len(carriers[sort])
      cs[other][vals[pos]]=p[source][x]
     for other,values in sorted(cs.items()):
      check(None not in values,'partial operation')
      for x,v in enumerate(values):keys[sort][x].append(v)
  q=tuple(canon(tuple(z) for z in keys[s]) for s in range(len(carriers)))
  if q==p:break
  check(sum(map(lambda z:len(set(z)),q))>sum(map(lambda z:len(set(z)),p)),'non-strict refinement')
  p=q;hist.append([len(set(z)) for z in p])
 if expected is not None:check(p==expected,'generated closure differs from proposed quotient')
 return {'contexts':contexts,'transport':transport is not None,'stages':hist,'record_count':sum(len(r) for _,_,r in rows),'unit_enabled_old_records':[name for name,r in RECORDS if r.is_identity()]}

def group_decoder():
 labels=tuple(product(range(4),repeat=2));ix={x:i for i,x in enumerate(labels)}
 m=tuple(tuple(ix[tuple((a+b)%4 for a,b in zip(x,y))] for y in labels) for x in labels)
 carriers,rows=build_records(m);units=unit_mask(carriers,0)
 obs=[tuple(tuple(labels[x] if r.rank()==1 else tuple(v%2 for v in labels[x]) for x in xs) for xs in C) for (_,r),C in zip(RECORDS,carriers)]
 for source,sorts,records in rows:
  forward={};concrete=[set() for _ in carriers[source]]
  for x,vals in records:
   fo=tuple(obs[s][v] for s,v in zip(sorts,vals));so=obs[source][x]
   if fo in forward:check(forward[fo]==so,'group graft depends on representative')
   else:forward[fo]=so
   concrete[x].add(fo)
  inverse=defaultdict(set)
  for f,s in forward.items():inverse[s].add(f)
  for x,so in enumerate(obs[source]):check(concrete[x]==inverse[so],'direct full-profile cut decoder')
 for s,values in enumerate(obs):
  decoder={}
  for x,v in enumerate(values):
   if v in decoder:check(decoder[v]==units[s][x],'unit decoder not exact')
   else:decoder[v]=units[s][x]
 generated=refinement(m,0,tuple(a%2 for a,b in labels),True,tuple(ix[(b,a)] for a,b in labels),tuple(canon(values) for values in obs))
 return {'generated_SCT_from_first_channel_parity':generated,'carrier_sizes':list(map(len,carriers)),'quotient_sizes':[len(set(z)) for z in obs],
         'full_record_count':sum(len(r) for _,_,r in rows),'direct_decoder_checks':sum(len(carriers[s]) for s,_,_ in rows)}

def main():
 # Exact old tags visibly distinguish a genuine unary identity from same-rank empty insertion.
 check(RECORDS[4][1].rank()==RECORDS[6][1].rank()==1,'rank control')
 check(RECORDS[4][1].is_identity() and not RECORDS[6][1].is_identity(),'full old unit control')
 check(RECORDS[0][1].rank()==RECORDS[1][1].rank()==0,'empty rank')
 check(not RECORDS[0][1].is_identity() and RECORDS[1][1].is_identity(),'nullary is not zero tree')
 m,e,seed=table_for_M4();cuts=refinement(m,e,seed,False);mixed=refinement(m,e,seed,True)
 result={'status':'Explicit-old-record finite checks passed',
         'old_records':[{'name':name,**asdict(r),'active_rank':r.rank(),'literal_identity':r.is_identity()} for name,r in RECORDS],
         'operation_count':len(operations()),'M4_C':cuts,'M4_SC':mixed,'rank_sensitive_C4_squared':group_decoder(),
         'scope':'Finite named subdiagram of terminal-grade edgeless old operations; every induced graft/cut whose factors/source belong to this catalogue is tested. Not all old records or all generated trees.',
         'correction':'Supersedes use of a hand-set identity mask on the size-only J=(2) sort. Whole-graph unary identities admit unit cuts at every component size.',
         'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
 out=Path(__file__).with_name('explicit_old_record_results.json');out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ('status','operation_count','M4_C','M4_SC','rank_sensitive_C4_squared')},indent=2))
if __name__=='__main__':main()
