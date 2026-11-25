"""Different physical release rules, same retained exclusion tests when mapped lawfully."""
from itertools import product
from random import Random
from obstruction import mask,smallest_cover

def rotor(t,h,own):
    # A mechanically retained local work right occupies the passage through
    # the final dwell tick, regardless of return of any radio acknowledgment.
    return t-own+1,h+own-1

def shutter(t,opens,own):
    # A powered rail gate is exclusively reserved while physically latched.
    # Opens is the actual scheduled reopening, not a receipt timestamp.
    return t-own+1,opens-t+own-1

def profiles(limit,space,exclusion):
    return {mask(limit,*exclusion(*x)) for x in space}

def replacement(n,rows,outcomes):
    # rows is a frozen witness index; each outcome is an admissible vector
    # of replacement source effects for the SAME external context value.
    full=(1<<n)-1
    old=list(map(lambda iv:mask(n,*iv),rows))
    expired=[]
    for rs in outcomes:
        masks=list(map(lambda iv:mask(n,*iv),rs))
        assert len(masks)==len(old)
        v=0
        for m in masks:v|=m
        expired.append(full&~v)
    return not any(expired),expired

def rectangular(n,choices):
    full=(1<<n)-1
    union=0
    for opts in choices:
        intersection=full
        for iv in opts:intersection&=mask(n,*iv)
        union|=intersection
    return union==full

def main():
    for d,n,a,h in product(range(1,6),range(1,12),range(-5,10),range(1,6)):
        assert mask(n,*rotor(a,h,d))==mask(n,*shutter(a,a+h,d))
    for n,d in product(range(1,12),range(1,6)):
        inputs=list(product(range(-5,10),range(1,6),(0,1)))
        new=list((s,s+h,metadata) for s,h,_ in inputs for metadata in range(3))
        p=profiles(n,inputs,lambda s,h,meta:rotor(s,h,d))
        q=profiles(n,new,lambda s,e,meta:shutter(s,e,d))
        assert p==q
    # Same status/report but command effect physically remained for one extra tick.
    assert mask(5,*rotor(1,2,1))!=mask(5,*shutter(1,4,1))
    # A shared mode swaps the roles occupying each interval. The rectangular
    # product invents contexts that were not authorized and weakens rejection.
    a=(0,2);b=(1,2)
    options=((a,b),(b,a))
    old=(a,b)
    assert replacement(3,old,options)==(True,[0,0])
    assert replacement(3,old,product(*options))==(False,[0,4,1,0])
    assert not rectangular(3,options)
    rng=Random(641172)
    for j in range(5000):
        n=rng.randrange(1,10)
        choices=tuple(tuple((rng.randrange(-3,n+3),rng.randrange(1,n+3)) for i in range(rng.randrange(1,4))) for k in range(rng.randrange(1,5)))
        rows=tuple(x[0] for x in choices)
        assert rectangular(n,choices)==replacement(n,rows,product(*choices))[0]
    print('4125 exact local primitive transport probes and 55 attained-profile checks')
    print('5000 rectangular reuse checks; coupled swap transports despite marginal failure')
if __name__=='__main__':main()
