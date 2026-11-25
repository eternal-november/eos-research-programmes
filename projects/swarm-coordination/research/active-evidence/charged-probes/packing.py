"""Exact common deadline of physical cleanup and received evidence."""
from charged import Source
from overlap import feasible
from math import inf
from itertools import product

def fees(r,j,d,s):
    # Each of r cleanup windows accepts floor(d/s) consecutive full
    # isolated trials with no extension. Up to one next per block costs
    # s - (d mod s); further trials in a block cost s each.
    a,b=divmod(d,s)
    overflow=max(0,j-r*a)
    return (s-b)*min(overflow,r) + s*max(0,overflow-r)

def common_deadline(z):
    k,d,s=z.max_erased,z.cooldown,z.spare_dur
    m=z.battery//z.battery_cost
    best=inf; witness=None
    for j in range(min(k,m)+1):
        r=k-j
        if r and not z.guard:continue
        for last in (0,1):
            if j+last>m:continue
            t=r*(1+d)+fees(r,j+last,d,s)+int(last==0)
            if t<best:best=t;witness=(j,last)
    return best,witness

def check():
    n=0
    for d,s,c,g,k,B in product(range(5),range(1,5),range(1,3),
                              (False,True),range(7),range(8)):
        z=Source(d,s,c,g,k,B)
        t,w=common_deadline(z)
        if t==inf:
            assert not feasible(z,100,100,True)
        else:
            assert not feasible(z,t-1,t-1,True) and feasible(z,t,t,True),(z,t,w)
        n+=1
    print(n,"exact common-horizon checks against active event solver")
    z=Source(4,1,1,True,5,3)
    print("five possible erasures, three isolated charges, total-time optimum",common_deadline(z))
    z=Source(7,2,1,True,2,1)
    assert common_deadline(z)==(9,(0,1)) or common_deadline(z)==(9,(1,0))
if __name__=="__main__":check()
