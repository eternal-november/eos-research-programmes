"""Independent continuous piecewise-affine LP check at all permitted knots."""
from actuation import *
from scipy.optimize import linprog
from random import Random

def lp(s,T,knots):
    x=sorted({F(0),T,*knots})
    n=len(x); c=[F(0)]*n; A=[];B=[]
    for i,(l,r) in enumerate(zip(x,x[1:])):
        d=r-l
        c[i]+=d/2;c[i+1]+=d/2
        v=[0]*n;v[i]=-1;v[i+1]=1
        A.append(v);B.append(float(s.accel*d))
        A.append([-w for w in v]);B.append(float(s.brake*d))
    A.append(list(map(float,c)));B.append(float(min(s.anchor,s.clearance)))
    bounds=[(float(s.speed),float(s.speed))]+[(0,float(s.vmax))]*(n-2)+[(0,0)]
    return linprog([-float(v) for v in c],A_ub=A,b_ub=B,bounds=bounds,method='highs')

def main():
    rng=Random(636193)
    for _ in range(520):
        a,b,V=[F(rng.randint(1,12),4) for _ in range(3)]
        v=V*rng.randrange(5)/4
        if rng.randrange(3)==0:a=F(0)
        T=F(rng.randrange(1,32),4)
        s=Side(v,V,a,b,F(rng.randrange(32),4),F(rng.randrange(32),4))
        fact=envelope(s,T)
        if fact is not None:
            r=lp(s,T,fact[3]+[T*i/5 for i in range(1,5)])
            assert r.success and abs(-r.fun-float(fact[1]))<1e-7
            positive(s,T,fact[0]);positive(s,T,fact[1]);positive(s,T,(fact[0]+fact[1])/2)
        else:
            # Give independently constructed LP the physical braking knee if within the horizon.
            t=v/b
            r=lp(s,T,[T*i/5 for i in range(1,5)]+[t] if t<T else [T*i/5 for i in range(1,5)])
            assert not r.success
    print("520 trajectory LP and continuous constructed-path checks")
if __name__=="__main__":main()
