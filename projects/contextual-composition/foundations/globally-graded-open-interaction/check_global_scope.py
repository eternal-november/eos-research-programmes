"""Finite exact native-control diagnostics, not higher coherence certification."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
law={w:F(0) for w in product(range(2),repeat=6)}
for x1,x2,r,s,t in product(range(2),repeat=5):
    law[x1,x2,r,r^x2,s,t]=F(1,32)
assert len(law)==64 and sum(p>0 for p in law.values())==32 and sum(law.values())==1
m1=defaultdict(F);m2=defaultdict(F)
for (x1,x2,y11,y12,y21,y22),p in law.items():
    m1[x1,y11,y12]+=p;m2[x2,y21,y22]+=p
assert len(m1)==len(m2)==8
assert set(m1.values())==set(m2.values())=={F(1,8)}
for x1,x2 in product(range(2),repeat=2):
    mass=sum(p for w,p in law.items() if w[:2]==(x1,x2))
    equal=sum(p for w,p in law.items() if w[:2]==(x1,x2) and w[2]==w[3])/mass
    assert mass==F(1,4) and equal==1-x2
    for i in range(2,6):
        assert sum(p for w,p in law.items() if w[:2]==(x1,x2) and w[i]==1)/mass==F(1,2)
# Each completed local GH trajectory is uniformly distributed on 8 points.
# But no local X1-only continuation row can match both full-prefix pair marginals.
for x1 in range(2):
    local_equal=sum(p for (x,a,b),p in m1.items() if x==x1 and a==b)/F(1,2)
    assert local_equal==F(1,2)
print('PASS: 64 raw points, 32 positive atoms; uniform local GH laws; same flat completed-trajectory coupling.')
print('PASS: all primitive conditional marginals fair; group1 equality conditional fullpast is 1-X2, not local1/2.')
# Parenthesized groupings preserve full q, not just pair marginals.
conditional={w[2:]:p/F(1,4) for w,p in law.items() if w[:2]==(0,1)}
charts=[lambda w:((w[0],w[1]),(w[2],w[3])),
        lambda w:(((w[0],w[1]),w[2]),w[3]),
        lambda w:(w[0],(w[1],(w[2],w[3])))]
def flatten(x):
    if isinstance(x,tuple): return sum((flatten(a) for a in x),())
    return (x,)
for chart in charts:
    encoded={chart(w):p for w,p in conditional.items()}
    assert {flatten(w):p for w,p in encoded.items()}==conditional
# Full grade maps preserve unused shapes as well, including arity0/4.
C={0:['unused0'],2:['used2'],4:['unused4']}
rho={c:'target'+str(n) for n,cs in C.items() for c in cs}
assert set(rho)=={'unused0','used2','unused4'}
print('PASS: full conditional q survives grouping charts; unused0/4 grade entries remain named.')
print('BOUNDARY: categorical pentagon/native tensor coherence are proved in text, not established by these finite charts.')
