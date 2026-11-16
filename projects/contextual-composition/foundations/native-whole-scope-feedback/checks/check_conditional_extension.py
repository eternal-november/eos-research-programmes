from fractions import Fraction as F
from itertools import product
import json
bits = list(product(range(2), repeat=2))
def law(t): return {(0,0):t,(0,1):F(1,2)-t,(1,0):F(1,2)-t,(1,1):t}
def marginal(q,i): return {b:sum(v for z,v in q.items() if z[i]==b) for b in range(2)}
D,A=law(F(1,2)),law(F(0))
for q in [D,A,law(F(1,4))]:
    assert sum(q.values())==1
    assert marginal(q,0)==marginal(q,1)=={0:F(1,2),1:F(1,2)}
def terminal(qzero):
    return {(b,x,y):(D if b==0 else qzero)[x,y]*(1-b) for b,x,y in product(range(2),repeat=3)}
assert terminal(D)==terminal(A)
assert D!=A
assert len(terminal(D))==8
source={(x,y):D[x,y] for x,y in bits}
pushed={(b,x,y):(source[x,y] if b==0 else F(0)) for b,x,y in product(range(2),repeat=3)}
assert pushed==terminal(D)==terminal(A)
# Finite test slice of the full fair-coupling interval.
polys=[law(F(i,8)) for i in range(5)]
def extensions(tests):
    return [p for p in polys if all(p==v for v in tests)]
assert len(extensions([]))==5
assert extensions([D,D])==[D]
assert extensions([D,A])==[]
# One covered decision plus one untested decision: 5 distinct lifts on this grid.
lifts=list(product(extensions([D]),extensions([])))
assert len(lifts)==5
# A covering compatible cone has one lift, an incompatible cone none.
assert len(list(product(extensions([D]),extensions([A]))))==1
assert len(list(product(extensions([D,A]),extensions([]))))==0
# Known anticipation baseline: P:X then fresh P:Y, while Q:Z can appear first.
# Z=Y, X independent fair preserves both local terminal trace marginals;
# conditional Y given Z is point mass, not primitive fair.
joint={(x,y,z):(F(1,4) if y==z else F(0)) for x,y,z in product(range(2),repeat=3)}
for x,y in product(range(2),repeat=2):
    assert sum(joint[x,y,z] for z in range(2))==F(1,4)
for z in range(2):
    den=sum(joint[x,y,z] for x,y in product(range(2),repeat=2))
    cond=sum(joint[x,z,z] for x in range(2))/den
    assert cond==1
print(json.dumps({'zero_history_obstruction':'PASS','raw_zero_atoms_retained':8,'grid_extension_fibre_counts':[5,1,0], 'known_anticipation_control':'PASS', 'scope':'finite exact rational witnesses; not proof certification'},indent=2))
