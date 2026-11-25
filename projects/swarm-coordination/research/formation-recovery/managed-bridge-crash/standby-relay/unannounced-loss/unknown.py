"""Fixed-source cut check, not a live crash or control script."""
from standby import (run,qvec,dot,sub,add,scale,sq,connected_components,Q,combinations)
import numpy as np

s,r,_,_=run(3)
R=Q('1.65'); d=Q('0.45')
def state(k,deleted):
    P={i:qvec(p) for i,p in enumerate(r.positions[k]) if r.active[k,i]}
    survivors=set(P)-{deleted}
    edges=[(i,j) for i,j in combinations(sorted(survivors),2)
           if sq(sub(P[i],P[j]))<R*R]
    return P,connected_components(sorted(survivors),edges)

def center(P,a,b):
    return scale(Q(1,2),add(P[a],P[b]))

def test(P,groups,x,radius):
    assert all(sq(sub(p,x))>d*d for p in P.values())
    assert all(any(sq(sub(P[i],x))<=radius**2 for i in G) for G in groups)

P,g1=state(0,1)
P3,g3=state(0,3)
assert P3==P and g1==[{0},{2,3,4}] and g3==[{0,1,2},{4}]
a,b=center(P,0,2),center(P,2,4)
test(P,g1,a,R);test(P,g3,b,R)
assert sq(sub(a,b))>d*d
assert sq(sub(P[0],P[4]))> (2*Q('1.7919229'))**2
x=center(P,0,4)
test(P,g1,x,Q('1.7919231'));test(P,g3,x,Q('1.7919231'))
print("Same initial cut: either loss individually feasible at 1.65; one relay for both needs",
      "1.7919229 to 1.7919231; two relays meet 1.65 with physical clearance.")
P2,g2=state(2645,1)
assert g2==[{0},{2,3,4,5}]
assert sq(sub(P[4],P2[0]))>(2*Q('2.0538875'))**2
x=scale(Q(1,2),add(P[4],P2[0]))
# This upper bound verifies only range and clearance AT the two cuts.
test(P,g3,x,Q('2.0538877'));test(P2,g2,x,Q('2.0538877'))
print("Either initial loss 3 or loss 1 at 26.45: radio-only common fixed range 2.0538875 to 2.0538877;",
      "at 1.65 the relay positions must differ by at least 0.8077750.")
