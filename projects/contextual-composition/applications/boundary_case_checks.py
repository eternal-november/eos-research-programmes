"""Exact finite regression checks for focused O6 cases D/G/H.
E's continuous integral is proved analytically, not by finite sampling.
Run: python boundary_case_checks.py
"""
from fractions import Fraction
from itertools import product

# D: retained nested receipt labels, native collapse, frame naturality.
labels = {'r': ['a','b'], 's': ['a','b']}
nested = [('receipt','r'), ('base','a'), ('receipt','r')]
def expand(xs):
    return [v for kind,x in xs for v in ([x] if kind=='base' else labels[x])]
assert expand(nested)==['a','b','a','a','b']
collapse={'r':'r','s':'r'}
assert all(labels[collapse[r]]==labels[r] for r in labels)
assert expand([(k,collapse[x] if k=='receipt' else x) for k,x in nested])==expand(nested)
for x in [0,1]:
    frame_then_expand=[(x,v) for kind,r in nested for v in ([r] if kind=='base' else labels[r])]
    assert frame_then_expand==[(x,v) for v in expand(nested)]
# 1->2 frame comparison is a proper inclusion on all retained receipts.
source={(0,r) for r in labels}; target={(x,r) for x in [0,1] for r in labels}
assert source < target

# G: finite field F_5 exact matrix and augmentation tests.
p=5
def A(l): return ((1,(1-l)%p),(0,l))
def mm(a,b): return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2))%p for j in range(2)) for i in range(2))
def mv(a,v): return tuple(sum(a[i][j]*v[j] for j in range(2))%p for i in range(2))
for l,m in product(range(p),repeat=2):
    assert mm(A(l),A(m))==A((l*m)%p)
for l,x,y in product(range(p),repeat=3):
    assert sum(mv(A(l),(x,y)))%p==(x+y)%p
assert mv(A(1),(0,1))==(0,1)
assert mv(A(0),(0,1))==(1,0)
assert mm(A(0),A(0))==A(0)
assert all(mv(A(0),(x,y))==mv(A(0),((x+y)%p,0)) for x,y in product(range(p),repeat=2))
# External-test invariant criterion a=b.
for a,b in product(range(p),repeat=2):
    invariant=all((a*mv(A(0),(x,y))[0]+b*mv(A(0),(x,y))[1])%p==(a*x+b*y)%p for x,y in product(range(p),repeat=2))
    assert invariant==(a==b)

# H: dependent-pair protocol and exact no-go arithmetic.
f={'r1':'red','r2':'red','b':'blue'}
g={'red':{'s':'ok'},'blue':{'t':'ok','u':'retry'}}
raw=[(r,s,g[f[r]][s]) for r in f for s in g[f[r]]]
assert len(raw)==4
assert [x[2] for x in raw]==['ok','ok','ok','retry']
assert {x[2] for x in raw}==set().union(*(set(g[b].values()) for b in set(f.values())))
assert {'ok'} < {'ok','retry'}
merged=(Fraction(2,3),Fraction(1,3)); uniform2=(Fraction(1,2),Fraction(1,2))
assert merged!=uniform2
print('PASS D: retained labels, collapse, fixed-frame labels, noninvertible parameter comparison')
print('PASS G: F_5 coefficient composition, augmentation, projection, exact external-test boundary')
print('PASS H: raw composition/support and exact 3-to-2 merge obstruction')
print('E: analytic Borel/kernel/integral proof in Case E of the main casebook; no simulation substituted')
