"""Exact finite diagnostics, not certificates of the infinite-path theorems."""
from fractions import Fraction as F
from itertools import product
paths={():F(1)}
for n in range(1,9):
 nxt={}
 for h,p in paths.items():
  success=F(1,4) if sum(h)%2==0 else F(3,4)
  nxt[h+(0,)]=p*(1-success);nxt[h+(1,)]=p*success
 paths=nxt
 assert sum(paths.values())==1
 assert paths[(0,)*n]<=F(3,4)**n
for i in range(3):
 hazard=sum(F(1,8) for a in product(range(2),repeat=3) if a[i] and sum(a)==1)
 assert hazard==F(1,2)*F(1,2)**2
corr={(0,0):F(1,2),(1,1):F(1,2)}
ind={a:F(1,4) for a in product(range(2),repeat=2)}
for coordinate in [0,1]:
 for bit in [0,1]:
  assert sum(p for a,p in corr.items() if a[coordinate]==bit)==sum(p for a,p in ind.items() if a[coordinate]==bit)
assert corr!=ind
print('PASS: dependent conditional-hazard finite tails, private lone-attempt bound, joint-square marginal counterboundary')
