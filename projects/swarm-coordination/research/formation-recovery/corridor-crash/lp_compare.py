# Independent continuous optimization over terminal positions + time.
from fractions import Fraction
from random import Random
from scipy.optimize import linprog
import contextlib,io
with contextlib.redirect_stdout(io.StringIO()):
    from replay import factor, local_domains

def continuous_minimum(xs,f,g,r):
    n=len(xs)
    rows=[];rhs=[]
    def con(entries,val):
        row=[0]*(n+1)
        for i,c in entries:row[i]=c
        rows.append(row);rhs.append(val)
    for i in range(n-1):
        con([(i,-1),(i+1,1)],r)
        con([(i,1),(i+1,-1)],-g)
    for i,x in enumerate(xs):
        con([(i,1),(n,-1)],x)
        con([(i,-1),(n,-1)],-x)
    bounds=[]
    for i,x in enumerate(xs):
        bounds.append((x,x) if i in (0,n-1) else ((0,f-g) if x<f else (f+g,xs[-1])))
    result=linprog([0]*n+[1], A_ub=rows,b_ub=rhs,bounds=bounds+[(0,None)],method="highs")
    if result.status==2:return None
    assert result.success, result
    return Fraction(float(result.fun)).limit_denominator(1024)

def solve(xs,f,g,r,T):
    ds=local_domains(xs,f,g,T)
    if r<g:return
    a,b=ds[0]
    if a>b:return
    prior=[(a,b)]
    for lo,hi in ds[1:]:
        a,b=max(lo,a+g),min(hi,b+r)
        if a>b:return
        prior.append((a,b))
    ys=[prior[-1][0]]
    for a,b in reversed(prior[:-1]):
        y=ys[-1]
        ys.append(max(a,y-r))
        assert ys[-1]<=min(b,y-g)
    return tuple(reversed(ys))

seen=0
rng=Random(20261124)
for _ in range(480):
    L=rng.randint(5,35)
    n=rng.randint(2,min(8,L-1))
    full=(0,*sorted(rng.sample(range(1,L),n)),L)
    f=rng.choice(full[1:-1]);xs=tuple(x for x in full if x!=f)
    g=rng.choice([1,Fraction(1,2),min(y-x for x,y in zip(full,full[1:]))])
    r=Fraction(rng.randint(1,18),2)
    T=continuous_minimum(xs,f,g,r)
    if T is None:
        assert not factor(xs,f,g,r,L)
    else:
        assert factor(xs,f,g,r,T)
        if T>0:assert not factor(xs,f,g,r,max(Fraction(0),T-Fraction(1,10000)))
        ys=solve(xs,f,g,r,T)
        assert ys and all(abs(y-x)<=T for x,y in zip(xs,ys))
        assert all(g<=y-x<=r for x,y in zip(ys,ys[1:]))
        for u in (0,Fraction(1,7),Fraction(3,4),1):
            pos=tuple((1-u)*x+u*y for x,y in zip(xs,ys))
            assert all(y-x>=g for x,y in zip(pos,pos[1:]))
            assert all(x<=f-g if x0<f else x>=f+g for x0,x in zip(xs,pos))
    seen+=1
for r in [2,3,4]:
    xs=(0,2,7,9);f=4;g=1
    print(f"range={r} exact tested LP minimum={continuous_minimum(xs,f,g,r)}")
print(seen,"continuous LP comparisons with exact rational certificates")
