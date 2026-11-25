"""Sharp partial-identification decisions when the actual effects are not linked."""
from fractions import Fraction as F
from itertools import product
from random import Random
from coupled import exact

def report_event(L,R):
    return tuple(max(F(0),l+r-1) for l,r in zip(L,R)),tuple(min(l,r) for l,r in zip(L,R))

def union_in_report(L,a,b):
    # a,b are joint masses within the same report, not conditional fractions.
    return tuple(max(x,y) for x,y in zip(a,b)),tuple(min(l,x+y) for l,x,y in zip(L,a,b))

def verdict(L,lower,upper,w,cap):
    lo=exact(L,lower,w);hi=exact(L,upper,w)
    return "passes every coupling" if hi<=cap else ("fails every coupling" if lo>cap else "requires coupled evidence")

def main():
    rng=Random(552856)
    ncheck=0
    for mode in ('report','union'):
        for _ in range(712):
            n=rng.randrange(2,5)
            L=[F(rng.randrange(1,5),4) for i in range(n)]
            if mode=='report':
                R=[F(rng.randrange(5),4) for i in range(n)]
                lo,hi=report_event(L,R)
            else:
                A=[F(rng.randrange(1+int(4*l)),4) for l in L]
                B=[F(rng.randrange(1+int(4*l)),4) for l in L]
                lo,hi=union_in_report(L,A,B)
            w=F(rng.randrange(10),10);cap=F(rng.randrange(11),10)
            choices=[tuple(F(x,4) for x in range(int(4*i),int(4*j)+1)) for i,j in zip(lo,hi)]
            exact_flags=[exact(L,V,w)<=cap for V in product(*choices)]
            obs=verdict(L,lo,hi,w,cap)
            assert obs==('passes every coupling' if all(exact_flags) else
                         ('fails every coupling' if not any(exact_flags) else 'requires coupled evidence'))
            ncheck+=1
    n=4;w=F(1,4);R=(F(1,2),F(3,8),F(3,8),F(3,8));L=(F(1,2),)*n
    lo,hi=report_event(L,R)
    assert verdict(L,lo,hi,w,F(1,2))=="requires coupled evidence"
    a=(F(1,4),F(1,8),F(1,8),F(1,8));b=(F(1,8),)*n
    lo,hi=union_in_report(L,a,b)
    assert verdict(L,lo,hi,w,F(1,2))=="requires coupled evidence"
    print(ncheck,'direct finite coupling ranges, no independence inferred; unresolved cases wait for actual evidence')
if __name__=='__main__':main()
