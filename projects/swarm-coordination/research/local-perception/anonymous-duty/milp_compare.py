"""Equal-information XOR integer optimisation, independent of cycle parity."""
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp, linear_sum_assignment
from random import Random
from itertools import combinations
from pinned_motion import exact

def run(n, edges, w, a, fixed):
    # Binary source vertices x and parity auxiliaries k. 
    # x_u + x_v = y + 2k, where y is the unshifted 0/1 orientation.
    m=len(edges)
    if m==0:return 0
    A=np.zeros((m,n+2*m))
    for i,(u,v) in enumerate(edges):
        A[i,u]=A[i,v]=1
        A[i,n+i]=-1;A[i,n+m+i]=-2
    bounds0=np.zeros(n+2*m)
    bounds1=np.ones(n+2*m)
    for i,b in fixed.items():
        bounds0[i]=bounds1[i]=b
    obj=np.zeros(n+2*m)
    for i,(c,b) in enumerate(zip(w,a)):
        obj[n+i]=c if b else -c
    out=milp(obj,integrality=np.ones(n+2*m),
             bounds=Bounds(bounds0,bounds1),
             constraints=LinearConstraint(A,0,0),
             options={'mip_rel_gap':0.0})
    assert out.status==0 and out.x is not None
    x=np.rint(out.x[:n]).astype(int)
    assert np.max(np.abs(x-out.x[:n]))<1e-7
    assert all(int(x[i])==b for i,b in fixed.items())
    val=sum(c*(b^int(x[u])^int(x[v])) for c,b,(u,v) in zip(w,a,edges))
    shift=sum(c for c,b in zip(w,a) if b)
    assert abs(shift-out.fun-val)<1e-6
    return val

def matching_regression():
    identities=('A','B','C','D')
    slots=('r1','r2','o1','o2')
    relation={k:('r1','o1') if k in ('A','B') else ('r2','o2') for k in identities}
    def check(bound_relation):
        costs=np.array([[(-int(i in ('A','B') and r.startswith('r'))) if r in bound_relation[i] else 100
                         for r in slots] for i in identities])
        a,b=linear_sum_assignment(costs)
        assert all(costs[i,j]<100 for i,j in zip(a,b))
        return -int(costs[a,b].sum())
    assert check(relation)==1
    assert check({i:slots for i in identities})==2
    print('4-track pure matching regression: protected demand 1 with physical pair exclusivity, 2 without')

def main():
    matching_regression()
    rng=Random(834);count=0
    for n in range(2,13):
        ee=list(combinations(range(n),2))
        for _ in range(15):
            rng.shuffle(ee)
            E=ee[:rng.randrange(min(len(ee),n+5)+1)]
            w=[rng.randrange(1,10) for _ in E]; a=[rng.randrange(2) for _ in E]
            pins={v:rng.randrange(2) for v in range(n) if rng.random()<.3}
            assert run(n,E,w,a,pins)==exact(n,E,w,a,pins)[0]
            count+=1
    print(count,'same-input integer solver vs exact parity summaries')
if __name__=='__main__':main()
