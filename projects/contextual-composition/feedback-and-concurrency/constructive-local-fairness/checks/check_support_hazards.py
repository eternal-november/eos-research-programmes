from itertools import product
from fractions import Fraction as F
A=list(product(range(2),repeat=2)); subsets=[(0,),(1,),(0,1)]
rectangles=[set(product(x,y)) for x,y in product(subsets,repeat=2)]
count=0
for legal_mask in range(16):
 legal={a for k,a in enumerate(A) if legal_mask>>k&1}
 for table in product((0,1),repeat=8):
  p={(a,d):table[2*k+d] for k,a in enumerate(A) for d in (0,1)}
  for B in rectangles:
   if not B<=legal:continue
   before=all(any(p[a,d]>0 for a in B) for d in (0,1))
   after=any(all(p[a,d]>0 for d in (0,1)) for a in B)
   before_h=min(sum(F(p[a,d],len(B)) for a in B) for d in (0,1))
   after_h=sum(F(min(p[a,d] for d in (0,1)),len(B)) for a in B)
   assert before==(before_h>0) and after==(after_h>0)
   if before:assert before_h>=F(1,len(B))
   if after:assert after_h>=F(1,len(B))
   count+=1
# Two enabled tasks require 00 and 11 under diagonal joint legality.
diagonal={(0,0),(1,1)}
assert not any(B<=diagonal and (0,0) in B and (1,1) in B for B in rectangles)
# Observing a fresh private action strictly increases adversarial power.
p=lambda a,d:int(a==d)
assert min(sum(F(p(a,d),2) for a in (0,1)) for d in (0,1))==F(1,2)
assert sum(F(min(p(a,d) for d in (0,1)),2) for a in (0,1))==0
print('PASS:',count,'legal support/table cases; adversary timing and nonrectangular legality boundaries')
