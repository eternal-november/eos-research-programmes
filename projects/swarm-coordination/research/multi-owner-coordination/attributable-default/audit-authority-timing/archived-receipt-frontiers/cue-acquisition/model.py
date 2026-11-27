from fractions import Fraction as F
from itertools import product
from math import comb

def value(n,g,k):
    assert 1<=g<n and 1<=k<=n
    if g==n-1:return F(1),F(1),None
    if k>g+1:return F(g,n),F(0),None
    b=n-k
    q=F(g,n-1) if b>=g else F(b*(n-g),b+n*(n-g-1))
    p=F(g+q,n)
    a=k*(p-q)/(1-q)
    assert max(0,g-b)<=a<=min(g,k)
    return p,q,a

def checks():
    z=0
    for n,g,k in ((n,g,k) for n in range(2,100)
                  for g in range(1,n) for k in range(1,n+1)):
        b=n-k
        p,q,a=value(n,g,k)
        if g==n-1:
            assert comb(n,n)==1 and p==q==1
        elif k>g+1:
            assert p==F(g,n) and q==0
        else:
            assert q+(1-q)*a/k==p
            assert (q*(g+1-k)+(1-q)*(g-a))/b==p
            if b>=g:
                assert p==F(g,n-1)
            else:
                assert p==F(b+g*(n-g-1),b+n*(n-g-1))
        z+=1
    return z

if __name__=='__main__':print(checks())
