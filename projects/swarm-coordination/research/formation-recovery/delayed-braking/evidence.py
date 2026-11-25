"""One-cut recovery with a cap revealed after motion must have begun."""
from actuation import F,integrate,envelope,positive,Side
from itertools import combinations
from random import Random
from scipy.optimize import linprog

def triangle(t,z):
    # largest integral with endpoint speeds 0,z (or z,0).
    assert 0<=z<=t
    return (t*t+2*t*z-z*z)/4

def value(t,r,root,z):
    z=F(z)
    # Tight possibility has remaining allowed progress root**2. z**2/2
    # is both the least prefix advance to reach z and minimum future braking.
    assert 0<=z<=min(t,r,root)
    x=min(triangle(t,z),root*root-z*z/2)
    return x+triangle(r,z),x

def certificate(T,t,root):
    assert 0<=t<=T and root>=0
    r=T-t
    h=min(t,r,root)
    cut=2*root-t
    zcand=[]
    if cut>=0:
        zcand.append(min(h,cut))
    if h>=max(0,cut):
        zcand.append(max(F(0),cut,min(h,r/3)))
    u,z,x=max((v,z,x) for z in zcand for v,x in [value(t,r,root,z)])
    return u,z,x

def witness(T,t,root,loose):
    r=T-t
    opt,z,x=certificate(T,t,root)
    cap=root*root
    assert z*z/2<=x<=triangle(t,z)
    assert x+z*z/2<=cap
    def build_pre():
        lo=lambda s:max(F(0),z-(t-s))
        hi=lambda s:min(s,z+t-s)
        ks=sorted({F(0),t,t-z,(t+z)/2})
        small,big=z*z/2,triangle(t,z)
        a=(x-small)/(big-small) if small<big else F(0)
        vel=lambda s:lo(s)*(1-a)+hi(s)*a
        assert vel(F(0))==0 and vel(t)==z and integrate(ks,vel)==x
        assert all(abs(vel(a)-vel(b))<=b-a for a,b in zip(ks,ks[1:]))
        return ks,vel
    k,p=build_pre()
    tight_s=Side(z,T,F(1),F(1),cap-x,cap-x)
    loose_s=Side(z,T,F(1),F(1),loose-x,loose-x)
    if r>0:
        for s,smax in ((tight_s,min(cap,opt)),(loose_s,min(loose,opt))):
            assert envelope(s,r)[1]+x==smax
            positive(s,r,smax-x)
    return opt,z,x

def two_branch_lp(T,t,M,L,N=20):
    # Direct finite-dimensional control LP. Two possible physical futures
    # share each prefix knot. No analytical critical points supplied.
    R=T-t
    time=(tuple(F(t)*i/N for i in range(N+1)),
          tuple(t+R*i/N for i in range(N+1)))
    grid=tuple(sorted(set(time[0]+time[1])))
    # Distinguish branch states strictly after the observation cut only.
    ids0={q:i for i,q in enumerate(grid)}
    n=len(grid); ids1=ids0.copy()
    for q in grid:
        if q>t:ids1[q]=n;n+=1
    A=[];B=[];targets=[]
    ends={ids0[0],ids0[T],ids1[T]}
    for ids,cap in ((ids0,M),(ids1,L)):
        c=[F(0)]*n
        for a,b in zip(grid,grid[1:]):
            d=b-a
            c[ids[a]]+=d/2;c[ids[b]]+=d/2
            v=[0]*n;v[ids[a]]=-1;v[ids[b]]=1
            A.extend((v,[-x for x in v]));B.extend((float(d),float(d)))
        A.append(list(map(float,c)));B.append(float(cap))
        targets.append(c)
    p=linprog([-float(x) for x in targets[1]],A_ub=A,b_ub=B,
              bounds=[(0,0) if i in ends else (0,float(T))
                      for i in range(n)],method='highs')
    assert p.success
    return -p.fun

def main():
    rng=Random(690413)
    for j in range(2600):
        T=F(rng.randrange(1,18),3)
        t=T*rng.randrange(11)/10
        m=F(rng.randrange(1,14),3)
        u,z,x=witness(T,t,m,m*m+T*T+1)
        for zz in (min(t,T-t,m)*F(i,64) for i in range(65)):
            assert value(t,T-t,m,zz)[0]<=u,(j,T,t,m,zz,z,value(t,T-t,m,zz),u)
        if j<90:
            numerical=two_branch_lp(T,t,m*m,m*m+T*T+1)
            # A fixed piecewise-affine grid is conservative and need not
            # contain the optimum switch times. Give its bounded gap.
            assert numerical<=float(u)+1e-7
            assert float(u)-numerical<=float(T*T)/100
    print('2600 exact constructive and sampled endpoint checks; 90 independent trajectory LP tests')
    for t,u in ((1,4),(2,F(7,3)),(3,F(4,3)),(4,1)):
        got=certificate(F(4),F(t),F(1))
        assert got[0]==u
        print('observation cut',t,'maximum loose-world travel',got)
    assert certificate(F(4),F(1),F(1))[0]>=3
    assert certificate(F(4),F(2),F(1))[0]<3
    print('both physical worlds feasible when known; correlated two-side join fails after one extra tick')

if __name__=='__main__':main()
