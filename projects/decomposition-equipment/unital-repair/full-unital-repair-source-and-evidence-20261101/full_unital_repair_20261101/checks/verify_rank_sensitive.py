#!/usr/bin/env python3
"""Independent rank-sensitive quotient check on finite active-size templates.
No all-old-profile theorem is claimed. Full shared-parent tuples and literal
zero-tree feasibility (only the unary identity profile) are retained.
"""
from collections import defaultdict
from itertools import product, combinations
from pathlib import Path
from hashlib import sha256
import json

class Failure(RuntimeError):pass
def check(c,m):
 if not c:raise Failure(m)
def comps(n):
 if n==0:yield ()
 for first in range(1,n+1):
  for tail in comps(n-first):yield (first,)+tail

def run(order,channels,bound):
 labels=tuple(product(range(order),repeat=channels));n=len(labels);ix={x:i for i,x in enumerate(labels)}
 table=tuple(tuple(ix[tuple((a+b)%order for a,b in zip(x,y))] for y in labels) for x in labels)
 types=tuple(p for leaves in range(1,bound+1) for p in comps(leaves))
 carriers={p:tuple(product(range(n),repeat=len(p))) for p in types}
 # Exact rank1 labels, parity labels independently at every branch of rank>=2.
 observed={p:tuple(tuple(labels[x] if len(p)==1 else tuple(c%2 for c in labels[x]) for x in xs)
                    for xs in carriers[p]) for p in types}
 indexes={p:{xs:i for i,xs in enumerate(carriers[p])} for p in types}
 operations=[]
 for source in types:
  rank=len(source)
  for breaks in product((False,True),repeat=rank-1):
   limits=(0,)+tuple(i+1 for i,b in enumerate(breaks) if b)+(rank,)
   children=tuple(source[a:b] for a,b in zip(limits,limits[1:]))
   outer=tuple(sum(child) for child in children)
   opsorts=(outer,)+children
   fibres=[set() for _ in carriers[source]];forward={};records=0
   for vals in product(*(range(len(carriers[p])) for p in opsorts)):
    parent=carriers[outer][vals[0]]
    childvals=[carriers[p][v] for p,v in zip(children,vals[1:])]
    result=tuple(table[a][b] for a,bs in zip(parent,childvals) for b in bs)
    resultid=indexes[source][result]
    factorobs=tuple(observed[p][v] for p,v in zip(opsorts,vals))
    outputobs=observed[source][resultid]
    if factorobs in forward:check(forward[factorobs]==outputobs,'substitution does not descend')
    else:forward[factorobs]=outputobs
    fibres[resultid].add(factorobs);records+=1
   quotient_fibres=defaultdict(set)
   for factorobs,outputobs in forward.items():quotient_fibres[outputobs].add(factorobs)
   representative={}
   for x,obs in enumerate(observed[source]):
    sig=frozenset(fibres[x])
    check(sig==frozenset(quotient_fibres[obs]),'direct concrete versus quotient cut decoder')
    if obs in representative:check(representative[obs]==sig,'joint cut not representative independent')
    else:representative[obs]=sig
   operations.append({'source':source,'outer':outer,'children':children,'records':records})
 # Zero-tree existence is literal source=unit in I=(1), not blanket rank condition.
 I=(1,);unit_tuple=(0,)
 for x,obs in enumerate(observed[I]):
  for y,other in enumerate(observed[I]):
   if obs==other:check((carriers[I][x]==unit_tuple)==(carriers[I][y]==unit_tuple),'unit feasibility')
 # Channel swaps and branch reversal preserve whole-profile equivalence.
 for p in types:
  target=p[::-1]
  transport={}
  for x,obs in enumerate(observed[p]):
   transformed=tuple(ix[labels[a][::-1]] for a in carriers[p][x][::-1])
   imageobs=observed[target][indexes[target][transformed]]
   if obs in transport:check(transport[obs]==imageobs,'transport failed')
   else:transport[obs]=imageobs
 return {'group':f'C{order}^{channels}','maximum_active_leaves':bound,
         'profiles':[{'type':p,'carrier':len(carriers[p]),'quotient':len(set(observed[p]))} for p in types],
         'operations':operations,'total_full_records':sum(x['records'] for x in operations),
         'passed':['literal zero-tree feasibility','joint cut full tuples','substitution whole inputs','channel and branch transport','direct concrete-versus-quotient relational decoder'],
         'scope':'Finite positive active-size templates with literal unary zero tree; all-profile and empty-slot extension needs separate theorem'}

if __name__=='__main__':
 result={'status':'Finite rank-sensitive controls passed','cases':[run(4,2,2),run(4,1,3)],
         'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
 path=Path(__file__).with_name('rank_sensitive_results.json');path.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'record_counts':[x['total_full_records'] for x in result['cases']]},indent=2))
