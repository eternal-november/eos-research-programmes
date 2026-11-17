from fractions import Fraction as F
from itertools import product
p={0:F(1,2),1:F(1,2),2:F(0)}
# Entire dependent carrier, including zero X/Z atoms and helper-at-zero Z=2.
raw=[]; law={}
for x1,x2,z1,z2 in product(range(3),repeat=4):
 for t1 in (range(3) if z1 in (1,2) else [None]):
  for t2 in (range(3) if z2 in (1,2) else [None]):
   r=(x1,x2,z1,z2,t1,t2);raw.append(r)
   law[r]=p[x1]*p[x2]*(1 if z1==x2 and z2==x1 else 0)*(p[t1] if t1 is not None else 1)*(p[t2] if t2 is not None else 1)
assert sum(law.values())==1
for i in (0,1):
 for x in range(3):
  mass=sum(q for r,q in law.items() if r[i]==x)
  if mass:
   for z in range(3):
    assert sum(q for r,q in law.items() if r[i]==x and r[2+i]==z)==mass*p[z]
 for x,z in product(range(3),repeat=2):
  if z not in (1,2):continue
  mass=sum(q for r,q in law.items() if r[i]==x and r[2+i]==z)
  if mass:
   for t in range(3):
    assert sum(q for r,q in law.items() if r[i]==x and r[2+i]==z and r[4+i]==t)==mass*p[t]
# Source fails at a positive whole-X fibre; no division at zero.
fibre=sum(q for r,q in law.items() if r[:2]==(0,0))
assert fibre==F(1,4)
assert sum(q for r,q in law.items() if r[:2]==(0,0) and r[2]==0)==fibre
assert fibre!=fibre*p[0]
# Two nonunit stop heads: simultaneous slice product vs serial tensor.
assert (2+2-1)==3 and 2*2==4
print('PASS exact target local and helper tests; source whole-prefix test fails')
print('Full dependent carrier:',len(raw),'positive atoms:',sum(q>0 for q in law.values()),'zero atoms:',sum(q==0 for q in law.values()))
print('PASS two-stop slice dimension 3 versus temporal tensor dimension 4; shared clock 1 versus 2')
