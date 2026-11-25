"""Exact finite and rational checks for an active support probe (Python 3)."""
from fractions import Fraction as Q
from itertools import product
from random import Random

def overlap(m, n, t, drift, error):
    d = [x-y for x,y in zip(m,n)]
    return all(abs(d[j]-d[i]) <= 2*drift*abs(t[j]-t[i])+4*error
               for i in range(len(t)) for j in range(i))

def common_trace(m, n, t, drift, error):
    # Upper envelope of downward Lipschitz cones from the lower endpoints.
    d = [y-x for x,y in zip(m,n)]
    z = [max(d[j]-2*error-2*drift*abs(t[i]-t[j])
             for j in range(len(t))) for i in range(len(t))]
    if any(abs(a-b)>2*error for a,b in zip(z,d)):
        return None
    a = [x+Q(c,2) for x,c in zip(m,z)]
    b = [y-Q(c,2) for y,c in zip(n,z)]
    y = [Q(x+w,2) for x,w in zip(a,b)]
    for signal, bias, ideal in [(m,z,a),(n,[-v for v in z],b)]:
        assert all(abs(y[i]-ideal[i])<=error for i in range(len(t)))
        assert all(abs(Q(bias[i]-bias[j],2))<=drift*abs(t[i]-t[j])
                   for i in range(len(t)) for j in range(i))
    return y

def brute(m,n,t,drift,error):
    # On integer data the cone construction gives an integer difference
    # trajectory. Here test existence by enumerating candidate differences.
    domains = [range(y-x-2*error,y-x+2*error+1) for x,y in zip(m,n)]
    return any(all(abs(z[j]-z[j-1])<=2*drift*(t[j]-t[j-1])
                   for j in range(1,len(t))) for z in product(*domains))

def schedule_bound(A,V,D,k,L):
    return max(0, (k-Q(L,V))*min(2*A,Q(V*D,2)))

def exact_grid(A,V,D,k,L):
    # Half-unit controls (2*V, 2*A units); exact one-tick lattice baseline.
    def go(path):
        if len(path)==D+1:
            if path[-1]==0:
                yield path
            return
        for x in range(max(-2*A,path[-1]-2*V),min(2*A,path[-1]+2*V)+1):
            if abs(x)<=2*V*(D+1-len(path)-1):
                yield from go(path+[x])
    return max(max(k*abs(Q(u-v,2))-L*(j-i)
                   for j,v in enumerate(p) for i,u in enumerate(p[:j+1]))
               for p in go([0]))

def main():
    comparisons=0
    for d in product(range(-4,5),repeat=3):
        for t in [(0,1,2),(0,1,3),(0,2,5)]:
            for L,e in product(range(3),repeat=2):
                assert overlap([0]*3,d,t,L,e)==brute([0]*3,d,t,L,e)
                assert (common_trace([0]*3,d,t,L,e) is not None)==overlap([0]*3,d,t,L,e)
                comparisons+=1
    print('integer history tests',comparisons)
    rng=Random(417)
    for _ in range(5000):
        N=rng.randrange(2,14)
        m,n=[[Q(rng.randrange(-30,30),rng.randrange(1,6)) for _ in range(N)] for _ in range(2)]
        t=sorted(rng.sample(range(100),N))
        L,e=[Q(rng.randrange(7),rng.randrange(1,6)) for _ in range(2)]
        assert (common_trace(m,n,t,L,e) is not None)==overlap(m,n,t,L,e)
    print('rational certificate tests',5000)
    grids=0
    for A,V,D,k,L in product(range(1,3),range(1,3),range(2,6),range(1,4),range(3)):
        g=exact_grid(A,V,D,k,L)
        bound=schedule_bound(A,V,D,k,L)
        assert 0<=g<=bound
        edge=min(Q(2*A),Q(V*D,2))
        if (edge/V).denominator==1 and ((D-edge/V)*V/2).denominator <= 2:
            # The explicit optimum may still have a half-tick earlier read;
            # only assert attainment when a path using 0 as one endpoint
            # fits, or both ±A extrema fit on integer arrival from rest.
            if edge<=A or (edge==2*A and A%V==0):
                assert g==bound, (A,V,D,k,L,g,bound)
        grids+=1
    print('exact grid schedules',grids)
    t=[1,3]
    assert not overlap([-1,1],[1,-1],t,Q(1,5),Q(3,4))
    assert overlap([-1,1],[1,-1],t,Q(1,5),Q(4,5))
    y=common_trace([-1,1],[1,-1],t,Q(1,5),Q(4,5))
    print('exact boundary common sensor trace',y)
    assert overlap([1],[-1],[3],0,0)
    assert not overlap([-1,1],[1,-1],t,0,Q(3,4))

if __name__=='__main__':
    main()
