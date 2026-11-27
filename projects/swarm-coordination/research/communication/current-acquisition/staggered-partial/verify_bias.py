from fractions import Fraction as F
from random import Random
from scipy.optimize import linprog
from bias import unconstrained,minimum_amplitude

def forward(xs,g,D,B):
    p=F(0)
    spans=[(-B,B)]
    steps=[]
    for i in range(len(xs)-1):
        p+=g[i]
        d=D*(xs[i+1]-xs[i])
        l,h=(-d,-d) if p>0 else (d,d) if p<0 else (-d,d)
        q,r=spans[-1]
        start,end=max(-B,q+l),min(B,r+h)
        if end<start:return None
        spans.append((start,end));steps.append((l,h))
    x=spans[-1][0]
    path=[x]
    for (l,h),(q,r) in zip(reversed(steps),reversed(spans[:-1])):
        low,high=max(q,x-h),min(r,x-l)
        assert low<=high
        x=low
        path.append(x)
    return list(reversed(path))

def scope_lp(xs,g,D,B):
    n=len(xs)
    mat=[];rhs=[]
    for i in range(n-1):
        delta=D*(xs[i+1]-xs[i])
        for s in (-1,1):
            a=[0]*n;a[i]=s;a[i+1]=-s
            mat.append(a);rhs.append(float(delta))
    r=linprog([-float(x) for x in g],A_ub=mat or None,b_ub=rhs or None,
              bounds=(-float(B),float(B)),method='highs')
    assert r.success
    return -r.fun

def main():
    r=Random(9102)
    n_cases=384
    required=0
    for _ in range(n_cases):
        n=r.randrange(2,10)
        xs=sorted(F(r.randrange(0,20),6) for _ in range(n))
        g=[F(r.randrange(-2,3),3) for _ in range(n-1)]
        g.append(-sum(g))
        D=F(r.randrange(0,7),7)
        width=minimum_amplitude(xs,g,D)
        lp,suff=unconstrained(xs,g,D)
        assert width<=suff
        a=forward(xs,g,D,width)
        assert all(-width<=x<=width for x in a)
        assert all(abs(a[i+1]-a[i])<=D*(xs[i+1]-xs[i]) for i in range(n-1))
        assert sum(x*y for x,y in zip(a,g))==lp
        assert abs(scope_lp(xs,g,D,width)-float(lp))<1e-9
        if width:
            assert forward(xs,g,D,width/2) is None
            assert scope_lp(xs,g,D,width/2)+1e-9<float(lp)
            required+=1
    print(n_cases,required)

if __name__=='__main__':main()
