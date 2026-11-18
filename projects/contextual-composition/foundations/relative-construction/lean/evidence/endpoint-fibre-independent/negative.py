from itertools import product
from math import factorial
# One-object category: all self-maps of {0,1,2}; identity-on-arrows reference.
M=list(product(range(3), repeat=3))
I=(0,1,2); c=(1,2,0); ci=(2,0,1)
def then(f,g):return tuple(g[i] for i in f)
def conj(f,k):return then(then(k,f),ci if k==c else c)
# Old left c; f; c^-1. Hence c is natural to right=id.
# Right control missing: both old endpoint actions conjugated by c;
# same component c (c commutes with its own powers), still natural.
# Component control missing: right fixed, instead choose left seen via inverse c.
def oldL(f):return conj(f,c)
def newR(f):return conj(f,c)
def newL(f):return conj(newR(f),c)
def wrongL(f):return conj(f,ci)
def natural(L,R,a):return all(then(L(f),a)==then(a,R(f)) for f in M)
def functor(F):return F(I)==I and all(F(then(f,g))==then(F(f),F(g)) for f,g in product(M,repeat=2))
assert all(functor(F) for F in (oldL,newL,newR,wrongL))
assert natural(oldL,lambda f:f,c) and natural(newL,newR,c) and natural(wrongL,lambda f:f,ci)
noR=sum(newL(f)!=oldL(f) for f in M); badC=sum(wrongL(f)!=oldL(f) for f in M)
assert noR>0 and badC>0 and not natural(wrongL,lambda f:f,c)
# Actual cancellation c; f; c^-1 uniquely determines each left action, with correct right action.
assert all(then(then(c,f),ci)==oldL(f) for f in M)
print('27 endomorphisms (6 units); omitting fixed right action with unchanged components alters',noR,'left maps; inverting component at fixed right action alters',badC,'left maps.')
V=list(product(range(2),repeat=2))
add=lambda a,b:tuple((x+y)%2 for x,y in zip(a,b))
shear=lambda a:(a[0],(a[1]+a[0])%2)
assert all(shear(add(a,b))==add(shear(a),shear(b)) for a,b in product(V,repeat=2))
assert all(shear(a)[0]==a[0] for a in V)
assert all(shear(a)==a for a in V if not a[0])
assert all(shear(a)!=a for a in V if a[0])
print('C2 x C2: shear and identity agree strictly on base and vertical fibre but disagree on both moving arrows.')
