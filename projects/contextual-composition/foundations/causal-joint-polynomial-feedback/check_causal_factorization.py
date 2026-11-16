from fractions import Fraction as F
from itertools import product
W=list(product(range(2),repeat=2)); Z=W
q={(w,z):F(int(z==(w[1],w[0])),4) for w,z in product(W,Z)}
assert sum(q.values())==1
for i,x,y in product(range(2),repeat=3):
    assert sum(v for (w,z),v in q.items() if w[i]==x and z[i]==y)==F(1,4)
p={w:sum(q[w,z] for z in Z) for w in W}
def causal(law,first):
    return all(sum(law[w,z] for z in Z if z[i]==y)==first[w]*F(1,2)
               for w,i,y in product(W,range(2),range(2)))
assert not causal(q,p)
# Coherent shared innovations conditional on the full already revealed history.
r={}
for w in W:
    for z in Z:
        # Diagonal or antidiagonal chosen by prior parity; still fair marginals.
        r[w,z]=F(int((z[0]^z[1])==(w[0]^w[1])),2)
shared={(w,z):p[w]*r[w,z] for w,z in product(W,Z)}
assert causal(shared,p)
assert any(r[w,(0,0)]!=F(1,4) for w in W)
# Distinct choices on zero-probability rows have identical evaluated law.
p0={w:F(w==(0,0)) for w in W}
r1={(w,z):F(1,4) for w,z in product(W,Z)}
r2={(w,z):(F(1,4) if w==(0,0) else F(z[0]==z[1],2)) for w,z in product(W,Z)}
assert r1!=r2
flat1={(w,z):p0[w]*r1[w,z] for w,z in product(W,Z)}
flat2={(w,z):p0[w]*r2[w,z] for w,z in product(W,Z)}
assert flat1==flat2 and causal(flat1,p0)
print('PASS: locally valid anticipative coupling fails prefix conditional test; causal shared repair; retained zero-row choice noninjectivity.')
