"""Two uncertain obstacle centers, one common response before confirmation."""
from math import pi, cos, sin, hypot, sqrt

def bounds(a,R,c,rho,b,v=1):
    assert 0<c<a<R and b>=rho
    assert hypot(a,b)<=R and a-c+rho<=R
    assert hypot(a+c,rho)<=R
    M=(R*R-rho*rho-(a+c)**2)/(2*(a+c))
    assert c<M<rho
    eta=sqrt(rho*rho-M*M)
    # From stationary start after a report: approach to lower semicircle,
    # traverse on the side away from the closer anchor, then finish.
    sufficient=(2*hypot(c,b-rho)+pi*rho)/v
    necessary=(b+eta)/v
    return eta,necessary,sufficient

def known(a,R,c,rho,b,sgn):
    beta=sgn*c
    A=[]
    for i in range(257):
        t=i/256
        A.append((t*beta,-b+t*(b-rho)))
    for i in range(257):
        theta=-pi/2+pi*i/256
        A.append((sgn*(c-rho*cos(theta)),rho*sin(theta)))
    for i in range(257):
        t=i/256
        A.append(((1-t)*beta,rho+t*(b-rho)))
    assert all(hypot(x+a,y)<=R+1e-12 and hypot(x-a,y)<=R+1e-12 and
               hypot(x-beta,y)>=rho-1e-12 for x,y in A)
    return A

if __name__=='__main__':
    a,R,c,rho,b=3,5,.5,1.75,3.5
    eta,n,s=bounds(a,R,c,rho,b)
    for side in (-1,1):known(a,R,c,rho,b,side)
    # Both worlds individually possible, but a common crossing would
    # hit one of the uncertainties at the entire horizontal band.
    for j in range(101):
        y=eta*(2*j-100)/101
        half=sqrt(R*R-y*y)-a
        for k in range(101):
            x=half*(2*k-100)/100
            assert min(hypot(x-c,y),hypot(x+c,y))<rho
    staged=c+pi*rho+hypot(c,b-rho)
    print('common lower band eta',eta,'necessary post-report time',n,'sufficient from stationary start',s)
    print('known-safe prefix to y=-rho needs',b-rho,'then the branch suffix takes',staged)
