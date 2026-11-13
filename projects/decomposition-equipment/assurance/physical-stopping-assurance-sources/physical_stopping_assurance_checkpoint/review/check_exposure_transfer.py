"""Exhaustive depth-two rational check of Q-weighted first-loss transfer.
Not a replacement for the general coupling proof."""
from fractions import Fraction as F
from itertools import product
values=[F(0),F(1,2),F(1)]
checks=0
for p in product(values,repeat=3):
 for q in product(values,repeat=3):
  # root branch modes: 0 terminal safe, 1 terminal loss, 2 live
  for modes in product(range(3),repeat=2):
   for leaves in product((0,1),repeat=4):
    def risk(k):
     answer=F(0)
     for branch in range(2):
      mass=k[0] if branch else 1-k[0]
      child=F(modes[branch]) if modes[branch]<2 else (1-k[1+branch])*leaves[2*branch]+k[1+branch]*leaves[2*branch+1]
      answer+=mass*child
     return answer
    exposure=abs(p[0]-q[0])
    for branch in range(2):
     if modes[branch]==2:
      exposure+=(q[0] if branch else 1-q[0])*abs(p[1+branch]-q[1+branch])
    assert risk(p)<=risk(q)+exposure
    checks+=1
print(f'PASS: {checks} exact stopped-tree exposure-transfer cases')
