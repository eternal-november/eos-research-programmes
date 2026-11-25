from fractions import Fraction as F
from itertools import product
from math import sqrt
p=lambda v:max(F(v),F(0))

def h(g,x,y,v,w):
    return (x+p(v)**2/2,x+g*y+p(v+g*w)**2/(2*(1+g)),x-g*y+p(v-g*w)**2/(2*(1+g)))

def feasible_corners(g,H,v,w):
    P=(v,v+g*w,v-g*w)
    L=(1,1+g,1+g)
    for a,b in product((-1,1),repeat=2):
        dn=(a,a+g*b,a-g*b)
        if all(s!=0 or z+p(z)*u/c<=0 for s,z,u,c in zip(H,P,dn,L)):
            return True
    return False

q=tuple(F(i,4) for i in range(-8,9))
boundary=0
for g,y,v,w in product(map(F,('1','1.25','2','3','5')),q,q,q):
    x=-max(h(g,0,y,v,w))
    H=h(g,x,y,v,w)
    assert max(H)==0
    assert feasible_corners(g,H,v,w)
    boundary+=1
bad=0
for g,v in product(map(F,('0.25','0.5','0.75','0.99')),q[9:]):
    # This lead velocity is in the open bad interval in all these cases.
    r=(1+g)/2
    assert g<r*r<1
    w=r*v/g
    a=p(v+g*w)**2/(2*(1+g)); b=p(v-g*w)**2/(2*(1+g))
    x=-(a+b)/2; y=(b-a)/(2*g)
    H=h(g,x,y,v,w)
    assert H[0]<0 and H[1:]==(0,0) and not feasible_corners(g,H,v,w)
    bad+=1

checks=0
q=tuple(F(i,8) for i in range(17))
for g,v,w,t in product(map(F,('1','1.25','2','3','5')),q,q,q):
    A=v+g*w; tc=min(t,A)
    pre=A*tc-tc*tc/2
    at=max(h(g,v*t-t*t/2,w*t,v-t,w))
    d=max(v*v/2,A*A/2-g*p(A-t)**2/(2*(1+g)))
    assert d==max(pre,at)
    checks+=1
print(f'viable_boundary_states={boundary} sharp_nonviable_states={bad} delay_formula_cases={checks}')
print(f'example_deadline={3-sqrt(15/2):.8f}')
