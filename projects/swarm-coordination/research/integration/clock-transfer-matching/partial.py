"""Common-clock matching with justified missing-event bounds and reserve costs."""
from fractions import Fraction as F
from itertools import combinations,permutations,product
from random import Random
from scipy.optimize import linear_sum_assignment
from offset_match import intervals

def cells(A):
    z=sorted({x for interval in A.values() for x in interval})
    return z+[F(a+b,2) for a,b in zip(z,z[1:])] if z else [F(0)]

def extension(n,m,k,edges,w,a,b,sign):
    z=n+m-k
    G={(i,j):sign*(w[i][j]-a[i]-b[j]) for i,j in edges}
    G.update({(i,j):0 for i in range(n) for j in range(m,z)})
    G.update({(i,j):0 for i in range(n,z) for j in range(m)})
    return z,G

def assignment(n,G):
    f=1+sum(abs(a) for a in G.values())
    assert n*f<2**48
    a,b=linear_sum_assignment([[G.get((i,j),2*f) for j in range(n)] for i in range(n)])
    P=tuple((int(i),int(j)) for i,j in zip(a,b))
    if any(e not in G for e in P):return None
    return P

def cost(P,G):return sum(G[e] for e in P)

def extremal(n,m,A,h,k,w,a,b):
    rows=[]
    fixed=sum(a)+sum(b)
    for x in cells(A):
        edges={ij for ij,(l,u) in A.items() if l<=x<=u}
        for want in range(h,k+1):
            z,G=extension(n,m,want,edges,w,a,b,1)
            P=assignment(z,G)
            if P is None:continue
            l=fixed+cost(P,G)
            z,G=extension(n,m,want,edges,w,a,b,-1)
            Q=assignment(z,G)
            assert Q is not None
            u=fixed-cost(Q,G)
            rows.append((l,u))
    return (min(z[0] for z in rows),max(z[1] for z in rows)) if rows else None

def direct(n,m,A,h,k,w,a,b):
    f=sum(a)+sum(b)
    vals=[]
    for g in range(h,k+1):
        for I in combinations(range(n),g):
            for J in permutations(range(m),g):
                E=tuple(zip(I,J))
                if not all(e in A for e in E):continue
                if E and max(A[e][0] for e in E)>min(A[e][1] for e in E):continue
                vals.append(f+sum(w[i][j]-a[i]-b[j] for i,j in E))
    return (min(vals),max(vals)) if vals else None

def main():
    A=intervals([0,2],[0,2],[[0,0],[0,0]],[[1,1],[1,1]],(-3,3))
    # Source 0 carries a one-unit old duty, 0 precise terminal release,
    # any other result prudently counts that duty still against source.
    w=[[0,1],[0,0]]
    a,b=[1,0],[0,0]
    assert extremal(2,2,A,2,2,w,a,b)==(0,0)
    assert extremal(2,2,A,1,2,w,a,b)==(0,1)
    assert extremal(2,2,{e:(-3,3) for e in A},2,2,w,a,b)==(0,1)
    rng=Random(7618);checks=0
    for n,m in product(range(1,6),repeat=2):
        for j in range(13):
            # offset intervals may originate in transport and observed receive cut.
            A={}
            for i,d in product(range(n),range(m)):
                if rng.random()<.7:
                    c=F(rng.randrange(-5,6),2)
                    A[i,d]=(c,c+F(rng.randrange(5),2))
            lo=rng.randrange(min(n,m)+1);hi=rng.randrange(lo,min(n,m)+1)
            w=[[rng.randrange(9) for d in range(m)] for i in range(n)]
            a=[rng.randrange(4) for i in range(n)]; b=[rng.randrange(4) for d in range(m)]
            assert extremal(n,m,A,lo,hi,w,a,b)==direct(n,m,A,lo,hi,w,a,b)
            checks+=1
    print(checks,'duration/custody cases: cardinality-window sweep agrees with exhaustive partial assignments')
    print('two known transfers force discharge; allowing one missing transfer can leave the old duty live')
if __name__=='__main__':main()
