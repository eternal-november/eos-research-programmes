"""Exact diagnostics for positive-history mixing and the affine zero-fibre obstruction."""
from fractions import Fraction as F
from itertools import product
bits=list(product(range(2), repeat=2))
diag={w:F(w[0]==w[1],2) for w in bits}
anti={w:F(w[0]!=w[1],2) for w in bits}
ind={w:F(1,4) for w in bits}
p={0:F(1,6),1:F(1,3),2:F(1,2),3:F(0)}
q={0:diag,1:anti,2:ind,3:diag}
f={0:0,1:0,2:1,3:2}; g={0:0,1:0,2:1}
def averaged(p,q,f,zero):
    pp={j:sum(v for i,v in p.items() if f[i]==j) for j in set(f.values())}
    qq={j:({w:sum(p[i]*q[i][w] for i in p if f[i]==j)/pp[j] for w in bits} if pp[j] else zero) for j in pp}
    return pp,qq
p1,q1=averaged(p,q,f,anti)
p2,q2=averaged(p1,q1,g,ind)
pd,qd=averaged(p,q,{i:g[f[i]] for i in p},diag)
assert p2==pd and q2[0]==qd[0]
assert q2[1]!=qd[1] and p2[1]==0
for j in p2:
    for w in bits:
        assert p2[j]*q2[j][w]==pd[j]*qd[j][w]
        assert p2[j]*q2[j][w]==sum(p[i]*q[i][w] for i in p if g[f[i]]==j)
# Positive target marginal laws stay fair under mixtures.
for law in list(q1.values())+list(q2.values())+list(qd.values()):
    for k in range(2):
        for b in range(2): assert sum(v for w,v in law.items() if w[k]==b)==F(1,2)
print('PASS: exact positive-history tower identity, leaf pushforward, primitive marginals.')
print('PASS: different zero control tables, identical evaluated zero raw probabilities.')
a,b=F(0),F(1)
assert (2*a+b)/3 != (a+b)/2
print('PASS: symmetric affine zero averaging fails 3-to-2-to-1 composition.')
print('BOUNDARY: finite diagnostics only; supplied coefficient-arrow hypothesis checked in proof, not synthesized from laws.')
