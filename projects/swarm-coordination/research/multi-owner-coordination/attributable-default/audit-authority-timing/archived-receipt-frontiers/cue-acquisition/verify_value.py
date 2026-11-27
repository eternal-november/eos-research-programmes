from itertools import combinations,product
import numpy as np
from scipy.optimize import linprog
from model import value

def direct(n,g,k):
    # All exact placements at the read/assignment cut; no use of formula.
    C=tuple(range(k))
    worlds=[(set(range(n)),)*g+({r},) for r in C]
    demands=[s for a in (g,g+1) for s in combinations(range(n),a)]
    def fits(S,view):
        if not S:return True
        return any(S[0] in A and fits(S[1:],view[:i]+view[i+1:])
                   for i,A in enumerate(view))
    choices=[S for S in demands if all(fits(S,V) for V in worlds)]
    ub=[[-int(a in S) for S in choices]+[1] for a in range(n)]
    m=len(choices)
    r=linprog([0]*m+[-1],A_ub=ub,b_ub=[0]*n,
              A_eq=[[1]*m+[0]],b_eq=[1],bounds=(0,1),method='highs')
    assert r.success
    return r.x[-1]

def main():
    z=0
    for n in range(2,9):
        for g,k in product(range(1,n),range(1,n+1)):
            p=value(n,g,k)[0]
            q=direct(n,g,k)
            assert abs(float(p)-q)<1e-9,(n,g,k,p,q)
            z+=1
    print(z)
if __name__=='__main__':main()
