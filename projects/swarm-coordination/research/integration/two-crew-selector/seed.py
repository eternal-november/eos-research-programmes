"""Exact data for optimal reliability with common and private randomness."""
from selector import path
from itertools import product,combinations
from fractions import Fraction as F

def success_sets(n):
    valid=[]
    for inner in product((0,1),repeat=n-1):
        w=(0,*inner,1)
        wrong=[i for i in range(n) if w[i]!=w[i+1]]
        if len(wrong)==1:valid.append((w,wrong[0]))
    return tuple(valid)

def check():
    checked=0
    for n in range(1,61):
        # Fixed common probabilities; each group of two refers to a single
        # varying local vertex, so only that party uses a private coin.
        bins=[tuple(range(j,min(j+2,n))) for j in range(0,n,2)]
        assert len(bins)==(n+1)//2
        failure=[F(0)]*n
        for b in bins:
            for e in b:failure[e]+=F(len(b),n)/len(b)
        assert failure==[F(1,n)]*n
        if n<=12:
            for (u,i),(v,j) in combinations(success_sets(n),2):
                w=tuple(u[k] if k%2==0 else v[k] for k in range(n+1))
                x=tuple(v[k] if k%2==0 else u[k] for k in range(n+1))
                exactly_one=lambda y:sum(a!=b for a,b in zip(y,y[1:]))==1
                assert (exactly_one(w) and exactly_one(x))==(abs(i-j)==1)
                checked+=1
    print(checked,'cross-party seed-support combinations; optimum uses exactly ceil(d/2) common outcomes with private coins on a path')
if __name__=='__main__':check()
