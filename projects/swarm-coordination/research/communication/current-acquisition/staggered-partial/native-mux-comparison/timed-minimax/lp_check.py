"""Independent primal set-membership calculation."""
from fractions import Fraction as F
from itertools import product
from scipy.optimize import linprog
from scan import G,TIMES,PLANS,radius,opt,recovery
from mux import M,rank

# Variables: four pin levels at each of the three conversion instants
# and the final cut, three common bias values, three read errors.
def support(Q,L,B,D,noise,T):
    n=22
    time=TIMES+(T,)
    eq=[]; rhs=[]; ub=[]; bounds=[]
    def row(*pieces):
        out=[0.]*n
        for k,v in pieces:out[k]=float(v)
        return out
    for j,q in enumerate(Q):
        eq.append(row(*((4*j+i,a) for i,a in enumerate(q)),(16+j,sum(q)),(19+j,1)))
        rhs.append(0.)
    for j in range(3):
        for i in range(4):
            d=L[i]*(time[j+1]-time[j])
            for s in (1,-1):
                ub.append(row((4*j+i,s),(4*(j+1)+i,-s)));bounds.append(float(d))
        if j<2:
            d=D*(time[j+1]-time[j])
            for s in (1,-1):
                ub.append(row((16+j,s),(17+j,-s)));bounds.append(float(d))
    box=[(None,None)]*16+[(-float(B),float(B))]*3+[(-float(x),float(x)) for x in noise]
    r=linprog(row(*((12+i,-g) for i,g in enumerate(G))),A_ub=ub,b_ub=bounds,
              A_eq=eq,b_eq=rhs,bounds=box,method='highs')
    assert r.success
    return -r.fun

def verify():
    # Count ordered protocols including repeats. If Q does not span G,
    # a constant four-pin shift in the kernel makes the error unbounded.
    finite=[]; tested=0
    cache={}
    for k in range(4):
        for js in product(range(8),repeat=k):
            sorted_modes=tuple(sorted(set(js)))
            if sorted_modes not in cache:
                Q=tuple(M[j] for j in sorted_modes)
                cache[sorted_modes]=rank(Q)==rank(Q+(G,))
            if cache[sorted_modes]:finite.append(js)
            tested+=1
    assert set(finite)=={r[0] for r in PLANS}
    radius_checks=0
    biases=[(20,d) for d in (0,1,3,4,5,10)]+[(1,2),(1,10),(0,10)]
    calibration=[((1,1,1,4),F(2),(F(1,4),)*3),
                 ((1,2,3,5),F(2),(0,0,0)),
                 ((0,0,0,1),F(3),(F(1,2),F(1,4),F(0)))]
    for B,D in biases:
        for L,T,noise in calibration:
            for js,Q,a in PLANS:
                exact=sum(radius(Q,a,L,B,D,noise,T))
                assert abs(float(exact)-support(Q,L,B,D,noise,T))<1e-8,(js,L,B,D,exact)
                radius_checks+=1
    return tested,len(finite),radius_checks
