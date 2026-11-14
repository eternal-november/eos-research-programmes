"""Finite exhaustive diagnostic of binary three-history projection criterion."""
from itertools import product,combinations
E=range(3)
count=0
for b in product(range(2),repeat=3):
 for j1 in product(range(2),repeat=3):
  for j2 in product(range(2),repeat=3):
   js=(j1,j2)
   for i1 in product(range(2),repeat=2):
    for i2 in product(range(2),repeat=2):
     infos=(i1,i2); fibres={f:[e for e in E if b[e]==f] for f in set(b)}
     cond=all(sum(len({j[e] for e in fibre})>1 for j in js)<=1 for fibre in fibres.values())
     for agent in range(2):
      for f,g in combinations(fibres,2):
       if infos[agent][f]==infos[agent][g]:cond &= len({js[agent][e] for e in fibres[f]+fibres[g]})==1
     admitted=True
     for pair in combinations(E,2):
      active={f:[e for e in pair if b[e]==f] for f in set(b[e] for e in pair)}
      for f,es in active.items():
       n=len(es)
       for a,c in product(range(2),repeat=2):
        joint=sum(j1[e]==a and j2[e]==c for e in es)
        x=sum(j1[e]==a for e in es); y=sum(j2[e]==c for e in es)
        admitted &= joint*n==x*y
      for agent in range(2):
       for f,g in combinations(active,2):
        if infos[agent][f]==infos[agent][g]:
         left=sum(js[agent][e] for e in active[f]);right=sum(js[agent][e] for e in active[g])
         admitted &= left*len(active[g])==right*len(active[f])
     assert cond==admitted,(b,js,infos)
     count+=1
print('PASS:',count,'binary three-history information projections; pair-supported identity policies detect exactly the criterion')
