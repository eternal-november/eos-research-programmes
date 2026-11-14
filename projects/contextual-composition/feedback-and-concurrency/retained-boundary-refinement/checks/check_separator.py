"""Exact finite diagnostic, not an exhaustive theorem verifier."""
from fractions import Fraction as F
from itertools import product
p=[F(1,4),F(1,4),F(1,2)]
beta=[0,0,1]
rows=[[F(1),F(0)],[F(0),F(1)],[F(1,3),F(2,3)]]
mass={z:sum(p[s] for s in range(3) if beta[s]==z) for z in set(beta)}
bar={z:[sum(p[s]*rows[s][x] for s in range(3) if beta[s]==z)/mass[z] for x in range(2)] for z in mass}
delta=sum(p[s]*sum(abs(rows[s][x]-bar[beta[s]][x]) for x in range(2))/2 for s in range(3))
def defect(L):
 total=F(0)
 for z in mass:
  lb=[sum(p[s]*L[s][y] for s in range(3) if beta[s]==z)/mass[z] for y in range(len(L[0]))]
  for x in range(2):
   for y in range(len(L[0])):
    a=sum(p[s]*rows[s][x]*L[s][y] for s in range(3) if beta[s]==z)
    b=mass[z]*bar[z][x]*lb[y]
    total+=abs(a-b)/2
 return total
for labels in product(range(2),repeat=3):
 L=[[F(int(labels[s]==y)) for y in range(2)] for s in range(3)]
 assert defect(L)<=delta
identity=[[F(int(s==y)) for y in range(3)] for s in range(3)]
assert defect(identity)==delta==F(1,4)
eps=[F(1,5),F(1,3),F(1,7)]
survive=F(1)
for e in eps:survive*=1-e
assert 1-survive<=sum(eps)
error=F(0)
for bits in product(range(2),repeat=3):
 prob=F(1)
 for b,e in zip(bits,eps):prob*=e if b else 1-e
 if any(bits):error+=prob
assert error==1-survive
print("PASS: separator data-processing finite cases and exact revealing-partner attainment")
print("PASS: sharp finite-horizon independent-error product bound")
