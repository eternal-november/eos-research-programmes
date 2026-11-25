"""Development probe: committed identity from one common clock offset."""
from fractions import Fraction as F
from itertools import permutations,product
from random import Random
from scipy.optimize import linear_sum_assignment

def intervals(starts,ends,lo,hi,bounds):
    n=len(starts);A={}
    x0,x1=bounds
    for i,j in product(range(n),repeat=2):
        e=ends[j]-starts[i]
        a,b=max(x0,e-hi[i][j]),min(x1,e-lo[i][j])
        if a<=b:A[i,j]=(a,b)
    return A

def exact_range(n,A,w):
    if n==0:return [0,0]
    def opt(e,sign):
        # Sentinel greater than sum of magnitudes of every finite cost.
        f=1+sum(abs(a) for row in w for a in row)
        assert f*n<2**48, "baseline floating-cost range exceeded"
        u,v=linear_sum_assignment([[sign*w[i][j] if (i,j) in e else 2*f
                                    for j in range(n)] for i in range(n)])
        if any((i,j) not in e for i,j in zip(u,v)):return None
        return sum(w[i][j] for i,j in zip(u,v))
    if not A:return None
    edges=sorted({z for value in A.values() for z in value})
    points=edges+[F(a+b,2) for a,b in zip(edges,edges[1:])]
    results=[]
    for x in points:
        E={k for k,(a,b) in A.items() if a<=x<=b}
        t=opt(E,1)
        if t is not None:results += [t,opt(E,-1)]
    return (min(results),max(results)) if results else None

def direct(n,A,w):
    vals=[]
    for P in permutations(range(n)):
        Z=list(enumerate(P))
        if not all(e in A for e in Z):continue
        if max(A[e][0] for e in Z)>min(A[e][1] for e in Z):continue
        vals.append(sum(w[i][j] for i,j in Z))
    return (min(vals),max(vals)) if vals else None

def main():
    s=[0,2];r=[0,2];lo=[[0,0],[0,0]];hi=[[1,1],[1,1]]
    A=intervals(s,r,lo,hi,(-3,3))
    # Cost = old assigned to region containing destination 0.
    w=[[1,0],[0,0]]
    assert len(A)==4
    assert exact_range(2,A,w)==direct(2,A,w)==(1,1)
    assert exact_range(2,{e:(0,1) for e in A},w)==(0,1)
    Astar={(0,0):(-1,0),(1,1):(0,1)}
    assert exact_range(2,Astar,w)==(1,1)
    print('two source identities, four feasible edges, but only the straight common-clock matching')
    print('the detached clock graph loses identification; a match may only exist at a point boundary')
    rng=Random(627)
    ntests=0
    for n in range(1,8):
        for _ in range(40):
            s=[F(rng.randrange(-8,9),2) for z in range(n)]
            r=[F(rng.randrange(-8,9),2) for z in range(n)]
            lo=[[F(rng.randrange(4),2) for _ in r] for _ in s]
            hi=[[g+F(rng.randrange(6),2) for g in z] for z in lo]
            A=intervals(s,r,lo,hi,(-3,3))
            w=[[rng.randrange(-3,5) for _ in r] for _ in s]
            assert exact_range(n,A,w)==direct(n,A,w)
            ntests+=1
    print(ntests,'clock-arrangement matching ranges agree with complete assignment enumeration')
if __name__=='__main__':main()
