"""Exploratory two-anchor lens geometry for a civil relay.
Use analytic path proof for all-time guarantees; sampling is a regression.
"""
from math import pi,asin,sqrt,cos,sin,hypot
from random import Random

def optimum(a,R,b,rho):
    assert 0<a<R and 0<rho<=b<=sqrt(R*R-a*a)
    if rho>R-a:return None
    return 2*sqrt(b*b-rho*rho)+2*rho*asin(rho/b)

def turn(a,R,b,rho):
    beta=asin(rho/b)
    u=(rho*cos(beta),-rho*sin(beta))
    v=(u[0],-u[1])
    out=[]
    for i in range(129):
        t=i/128
        out.append((t*u[0],(1-t)*(-b)+t*u[1]))
    for i in range(129):
        t=-beta+2*beta*i/128
        out.append((rho*cos(t),rho*sin(t)))
    for i in range(129):
        t=i/128
        out.append(((1-t)*v[0],(1-t)*v[1]+t*b))
    return out

def main():
    for r in (1.9,2.0,2.1):
        print('anchor half spacing 3, radio 5, clearance',r,'length',optimum(3,5,3.5,r))
    rng=Random(827);n=0
    for _ in range(80):
        R=rng.uniform(3,10);a=rng.uniform(.1,.8)*R;rho=(R-a)*rng.uniform(.01,1)
        b=rng.uniform(rho,sqrt(R*R-a*a))
        length=optimum(a,R,b,rho)
        Q=turn(a,R,b,rho)
        assert all(hypot(x+a,y)<=R+1e-10 and hypot(x-a,y)<=R+1e-10 for x,y in Q)
        assert all(hypot(x,y)>=rho-1e-10 for x,y in Q)
        approx=sum(hypot(x-u,y-v) for (x,y),(u,v) in zip(Q,Q[1:]))
        assert approx<=length+1e-12 and length-approx<1e-3
        n+=1
    print(n,'independent path-length/sampled-constraint checks; samples are not continuous certificates')
if __name__=='__main__':main()
