#!/usr/bin/env python3
"""Third, purely combinatorial coverage calculation; imports no cut checker."""
from itertools import product
from math import comb
from pathlib import Path
import json

def mul(p,q):
    z=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):z[i+j]+=a*b
    return z

poly=[0,1]
for depth in range(3):
    square=mul(poly,poly)
    square[0]+=1
    for i,a in enumerate(poly):square[i]+=a
    poly=square

by_m={}
for m,g in [(0,1),(1,1),(2,2),(3,8)]:
    cuts=g*sum(n**m*comb(n+3,2) for n in range(4))
    refinements=0
    for n in range(1,4):
      for chain in product(range(3),repeat=n+1):
        if tuple(sorted(chain))!=chain:continue
        for i in range(n):
          a,b=chain[i:i+2]
          for s in range(m+1):
            assignments=comb(m,s)*(n-1)**(m-s)
            inner=int(s==0 and a==b)+1+2**s*(b-a+1)
            refinements+=g*assignments*inner
    by_m[m]={'cuts':cuts,'single_occurrence_refinements':refinements}

graph_labels=lambda L:sum((1<<(m*(m-1)//2))*L**m for m in range(4))
result={
  'method':'Combinatorial coefficients only; no author or independent checker imports.',
  'by_graph_size':by_m,
  'cuts':sum(v['cuts'] for v in by_m.values()),
  'single_occurrence_refinements':sum(v['single_occurrence_refinements'] for v in by_m.values()),
  'canonical_nested_restrictions':sum((1<<(m*(m-1)//2))*3**m for m in range(4)),
  'shape_leaf_histogram':dict(enumerate(poly)),
  'shapes':sum(poly),
  'graph_shape_label_assignments':sum(c*graph_labels(L) for L,c in enumerate(poly)),
  'interface_shape_chains':sum(c*comb(L+3,2) for L,c in enumerate(poly)),
  'full_typed_cases':sum(c*comb(L+3,2)*graph_labels(L) for L,c in enumerate(poly)),
}
assert result['cuts']==4395 and result['single_occurrence_refinements']==57156
assert result['shapes']==183 and result['full_typed_cases']==2745411
path=Path(__file__).with_name('combinatorial_counts.json')
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
