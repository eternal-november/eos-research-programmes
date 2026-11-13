#!/usr/bin/env python3
"""Exact regression checks; standard library only. Run python3 check.py."""
from fractions import Fraction as Q
import json

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def scale(c,a): return tuple(c*x for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def sub(a,b): return add(a,scale(-1,b))
def mv(A,v): return tuple(dot(r,v) for r in A)
def trans(A): return tuple(zip(*A))
def proj(x,v): return sub(v,scale(dot(x,v),x))
def arc(a,b,p): return add(scale(-dot(p,b),a),sub(p,scale(dot(p,b),b)))
e1,e2,e3=(1,0,0),(0,1,0),(0,0,1)
assert arc(e3,e1,arc(e2,e3,arc(e1,e2,e2)))==e3
assert sub(scale(dot(e3,e3),e2),scale(dot(e2,e3),e3))==e2
# moving-line tangent decomposition and dual pairing at x=2/3
x=Q(2,3); p=(Q(3),Q(2)); v=Q(5); z=(Q(7),Q(14,3)); ell=(Q(2),Q(-3)); lx=Q(11)
h=scale(p[0]*v/(1+x*x),(-x,Q(1))); dp=add(h,z)
assert dot((-x,1),dp)==v*p[0]
b=lx+dot(ell,scale(p[0]/(1+x*x),(-x,Q(1))))
g=sub(ell,scale(dot((-x,1),ell)/(1+x*x),(-x,Q(1))))
assert lx*v+dot(ell,dp)==b*v+dot(g,z)
# Independently differentiate the actual framed loss L=p1+p2.
# B(theta) gives (1+x)*theta; scaled frame gives (1+x)^2*theta_tilde.
def polymul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,w in enumerate(b): c[i+j]+=u*w
    return c
def derivative_at_zero(coefficients):
    return coefficients[1] if len(coefficients)>1 else Q(0)
theta=Q(3); B1=[Q(1)]; B2=[Q(0),Q(1)]; frame_scale=[Q(1),Q(1)]
loss_old=[theta,theta]
loss_new=polymul(frame_scale,loss_old)
assert loss_old[0]==loss_new[0]==theta
assert derivative_at_zero(loss_old)==theta
assert derivative_at_zero(loss_new)==2*theta
# horizontal correction d(theta_tilde)/dx=-theta cancels the extra term
assert derivative_at_zero(loss_new)-theta==derivative_at_zero(loss_old)
# Guard the original wrong example: L=p2 has equal derivatives at zero.
old_p2=[Q(0),theta]; new_p2=polymul(frame_scale,old_p2)
assert derivative_at_zero(old_p2)==derivative_at_zero(new_p2)==theta
# rational point on sphere, exact tangent blocks
x=(Q(1,3),Q(2,3),Q(2,3)); assert dot(x,x)==1
p=proj(x,(1,2,4)); v=proj(x,(3,1,2)); z=proj(x,(2,5,1)); eta=proj(x,(2,3,7)); beta=proj(x,(1,4,3))
M=((1,2,0),(0,1,3),(2,0,1)); N=((2,0,1),(1,3,0),(0,2,1))
def F(M,p): return proj(x,mv(M,p))
def K(M,p,v): return sub(scale(-dot(x,mv(M,p)),v),scale(dot(v,p),proj(x,mv(M,x))))
def V(M,z): return F(M,z)
def Kstar(M,p,eta): return sub(scale(-dot(x,mv(M,p)),eta),scale(dot(eta,proj(x,mv(M,x))),p))
def Vstar(M,eta): return proj(x,mv(trans(M),eta))
q=F(M,p); dp=add(K(M,p,v),V(M,z)); dq=add(K(N,q,v),V(N,dp))
# Independent ambient differentiation, with horizontal input dp0
h=scale(-dot(v,p),x); dP=lambda w: sub(scale(-dot(x,w),v),scale(dot(v,w),x))
dq1=add(dP(mv(M,p)),proj(x,mv(M,h)))
dq2=add(dP(mv(N,q)),proj(x,mv(N,dq1)))
assert proj(x,dq2)==add(K(N,q,v),V(N,K(M,p,v)))
b1=add(beta,Kstar(N,q,eta)); e1_=Vstar(N,eta)
b0=add(b1,Kstar(M,p,e1_)); e0=Vstar(M,e1_)
assert dot(beta,v)+dot(eta,dq)==dot(b0,v)+dot(e0,z)
assert K(M,p,v)!=(0,0,0)
print(json.dumps({'status':'pass','arithmetic':'exact rational','checks':['constraint and adjoint','frame dependence','spherical holonomy','curvature witness','two-layer ambient/block equality','reverse composition','nonzero cross term']},indent=2))
