from fractions import Fraction as F
import json
# Fixed root, two deterministic skeletons: convex relaxation has an extra point.
legal = {(F(1), F(0)), (F(0), F(1))}
mixed = (F(1,2), F(1,2))
assert sum(mixed)==1 and mixed not in legal
# A selected all-raw row includes its zero terminal successor.
raw={'positive','zero'}
weights={'positive':F(1),'zero':F(0)}
assert sum(weights.values())==1
assert {'positive'} != raw
# Nontrivial conditional admission with paid z, request seed x.
# Paid marginal fair, each seed conditional paid fair: only uniform joint.
# Global sibling y is allowed to correlate with x, but must not enter D=z.
atoms=[(z,x,y) for z in (0,1) for x in (0,1) for y in (0,1)]
def comps(n,k):
    if k==1:
        yield (n,); return
    for i in range(n+1):
        for r in comps(n-i,k-1): yield (i,)+r
def direct(q):
    for z in (0,1):
        mass=sum(q[i] for i,a in enumerate(atoms) if a[0]==z)
        if mass != F(1,2): return False
        for x in (0,1):
            v=sum(q[i] for i,a in enumerate(atoms) if a[:2]==(z,x))
            if v/mass != F(1,2): return False
    return True
def homogeneous(y,m):
    for z in (0,1):
        beta=sum(y[i] for i,a in enumerate(atoms) if a[0]==z)
        if beta != m/2: return False
        for x in (0,1):
            v=sum(y[i] for i,a in enumerate(atoms) if a[:2]==(z,x))
            if 2*v != beta: return False
    return True
count=admitted=0
for c in comps(4,8):
    q=tuple(F(v,4) for v in c); count+=1
    for m in (F(1),F(1,3)):
        assert direct(q)==homogeneous(tuple(m*v for v in q),m)
    admitted+=direct(q)
assert homogeneous((F(0),)*8,F(0))
assert not direct((F(1),)+(F(0),)*7) # Zero mass equations cannot select a legal q.
# Two fair-seed laws differ in hidden sibling correlations, both legal.
qdiag=tuple(F(1,4) if x==y else F(0) for z,x,y in atoms)
qanti=tuple(F(1,4) if x!=y else F(0) for z,x,y in atoms)
assert direct(qdiag) and direct(qanti) and qdiag!=qanti
# Their weighted successor flow reconstructs the exact whole law at positive mass.
for q in (qdiag,qanti):
    m=F(2,5); y=tuple(m*v for v in q)
    assert tuple(v/m for v in y)==q
# Full-law labels prevent offpolicy alternatives from colliding.
selected=('mu','root',qdiag)
unselected=('mu','root',qanti)
assert selected!=unselected
p={selected:'stop',unselected:'c0'}
p2={selected:'stop',unselected:'c1'}
assert p[selected]==p2[selected] and p!=p2
result={'deterministic_selector_not_convexified':'PASS','zero_raw_presence':'PASS',
'conditional_laws_enumerated':count,'admitted_laws':admitted,
'positive_homogeneous_admission_and_reconstruction':'PASS',
'zero_mass_does_not_supply_admitted_selector':'PASS','offpolicy_law_labels':'PASS',
'scope':'finite scalar/support probes; complete-control reconstruction and actual decorations remain written proof'}
print(json.dumps(result,indent=2))
