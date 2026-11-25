"""An actual-effect/camera cut; same likelihood can conceal different physical liability."""
from collections import namedtuple
from fractions import Fraction as F
from itertools import product
from random import Random

Row=namedtuple("Row","label phase report spent outstanding future")

def interpreted_action(label,phase,configuration,future):
    # Physical source model: earlier incomplete sample line may make an
    # additional contact at tick 2. Installing one of two calibrated latch
    # paths can close it at tick 1 or only at tick 3. Each has the same
    # report distribution and amount of delayed closure; different phases.
    # Earlier confirmed physical contact at tick 0 cannot be canceled.
    spent=int(label==0 and phase==0)
    at=1 if ((configuration=="green-fast")==(phase<4)) else 3
    if configuration=="overlap":
        at=3 if phase==1 else 1
    outstanding=int(phase in range(1,7) and at>2)
    report="green" if phase<4 else "amber"
    # Potential new transfer closes physically at tick 4, not at old cancel.
    new=int(future is not None and phase==future)
    return Row(label,phase,report,spent,outstanding,new)

def trace(config,future,n):
    return [interpreted_action(label,phase,config,future)
            for label,phase in product(range(n),range(8))]

def joint(rows,report,event,n):
    L=[F(0)]*n;C=[F(0)]*n
    count=[sum(r.label==i for r in rows) for i in range(n)]
    for r in rows:
        if r.report==report:
            p=F(1,count[r.label]);L[r.label]+=p
            if event(r):C[r.label]+=p
    return tuple(L),tuple(C)

def exact(L,C,w):
    assert all(0<=c<=l for c,l in zip(C,L)) and sum(L)>0 and 0<=w<1
    a=(1-w)/len(L)
    return max((a*sum(C)+w*c)/(a*sum(L)+w*l) for l,c in zip(L,C))

def cut(L,C,w,q):
    a=(1-w)/len(L)
    signed=[c-q*l for l,c in zip(L,C)]
    return a*sum(signed)+w*max(signed)<=0

def direct(rows,report,event,n,w):
    # Enumerate weights on all physical rows separately under each fixed law;
    # normalize once after selecting the actual received report.
    base=(1-w)/n
    scores=[]
    for j in range(n):
        count=[sum(r.label==i for r in rows) for i in range(n)]
        sample=[(r,(base+(w if j==r.label else 0))/count[r.label]) for r in rows if r.report==report]
        scores.append(sum(p for r,p in sample if event(r))/sum(p for r,p in sample))
    return max(scores)

def union(r):return r.spent or r.outstanding or r.future
def old(r):return r.spent or r.outstanding
def future(r):return r.future

def main():
    n=4;w=F(1,4)
    a,b=trace('green-fast',2,n),trace('amber-fast',2,n)
    aL,aC=joint(a,'green',union,n);bL,bC=joint(b,'green',union,n)
    assert aL==bL
    p,q=exact(aL,aC,w),exact(bL,bC,w)
    assert p==F(23,64) and q==F(55,64) and p<F(1,2)<q
    for i in range(n):
        assert sum(old(r) for r in a if r.label==i)==sum(old(r) for r in b if r.label==i)
    r1,r2=trace('overlap',1,n),trace('overlap',2,n)
    assert joint(r1,'green',old,n)==joint(r2,'green',old,n)
    assert joint(r1,'green',future,n)==joint(r2,'green',future,n)
    x,y=[exact(*joint(r,'green',union,n),w) for r in (r1,r2)]
    assert x==F(23,64) and y==F(39,64)
    print('equal report likelihood and unconditional old exposure, conditional union risk',p,q)
    print('equal old and new conditional marginals, different overlap',x,y)
    print('admission at one half must preserve both physical correlations')
    rng=Random(83913);cases=0
    for _ in range(2200):
        n=rng.randrange(2,8)
        rs=tuple(Row(i,k,'G' if k==0 or rng.randrange(2) else 'A',
                     rng.randrange(2),rng.randrange(2),rng.randrange(2))
                  for i in range(n) for k in range(rng.randrange(2,10)))
        w=F(rng.randrange(20),20);c=F(rng.randrange(21),20)
        cand=joint(rs,'G',union,n)
        assert exact(*cand,w)==direct(rs,'G',union,n,w)
        assert cut(*cand,w,c)==(exact(*cand,w)<=c)
        cases+=1
    print(cases,'physical-row replay versus exact per-threshold law envelope')
if __name__=='__main__':main()
