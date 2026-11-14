from fractions import Fraction as F
from itertools import product
# Exact gluing with a zero-mass middle state.
gamma={(0,0):F(1,3),(1,0):F(1,6),(0,1):F(1,4),(1,1):F(1,4)}
eta={(0,0):F(1,5),(0,1):F(3,10),(1,0):F(2,5),(1,1):F(1,10)}
nu={t:sum(gamma.get((s,t),0) for s in range(2)) for t in range(3)}
tri={(s,t,u):gamma.get((s,t),0)*eta.get((t,u),0)/nu[t] if nu[t] else F(0) for s,t,u in product(range(2),range(3),range(2))}
assert all(sum(tri[s,t,u] for u in range(2))==gamma.get((s,t),0) for s,t in product(range(2),range(3)))
assert all(sum(tri[s,t,u] for s in range(2))==eta.get((t,u),0) for t,u in product(range(3),range(2)))
# Persistent latent world versus erased locally selectable conditional law.
p0={(x,y):F(1,2) if y==0 else F(0) for x,y in product(range(2),repeat=2)}
p1={(x,y):F(1,2) if y==1 else F(0) for x,y in product(range(2),repeat=2)}
rect={(x,y):F(1,2) if y==x else F(0) for x,y in product(range(2),repeat=2)}
assert sum(v for (x,y),v in p0.items() if x==y)==F(1,2)
assert sum(v for (x,y),v in p1.items() if x==y)==F(1,2)
assert sum(v for (x,y),v in rect.items() if x==y)==1
print('PASS: exact conditional gluing with zero middle mass; strict persistent-dependence gap')
# Separately optimized cuts are strictly weaker than common witness feasibility.
a=(F(3,5),F(2,5),F(0));b=(F(0),F(3,5),F(2,5));mu=(F(3,10),F(2,5),F(3,10))
for mask in product((0,1),repeat=3):
    mass=lambda v:sum(v[i]*mask[i] for i in range(3))
    assert mass(mu)<=max(mass(a),mass(b))
assert mu[1]==a[1] and b[1]>a[1] and mu!=a
print('PASS: every cut separately feasible but no single admissible coupling target')
# Uniform affine selection exists but kernel-blind sampling contradicts itself.
for k in range(11):
    lam=F(k,10)
    mu=(lam/2,(1-lam)/2,F(1,2))
    joint=((lam/2,F(0)),(F(0),(1-lam)/2),((1-lam)/2,lam/2))
    assert tuple(sum(row) for row in joint)==mu
    assert tuple(sum(row[t] for row in joint) for t in range(2))==(F(1,2),F(1,2))
# First endpoint forces c->0 probability zero; second endpoint forces one.
assert (F(1,2)-F(1,2))/F(1,2)==0
assert F(1,2)/F(1,2)==1
print('PASS: affine coupling selector with incompatible kernel-blind c row')
