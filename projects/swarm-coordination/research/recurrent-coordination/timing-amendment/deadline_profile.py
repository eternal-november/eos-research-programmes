"""Old effects and mutable future mechanical minima, single stream."""
from itertools import combinations,product
from random import Random

def earliest(d,expiry,previous,h):
    """d includes authorized mechanical minimum for each phase in range(h)."""
    z=[];t=previous
    for g,e in enumerate(expiry):
        t=max(0, e, t+d[g])
        z.append(min(h,t))
    return tuple(z)

def legal(P, d, expire, previous, recurrent):
    K=len(expire)
    for i,t in enumerate(P):
        if t<(previous if i==0 else P[i-1])+d[i]:return False
        if i<K and t<expire[i]:return False
        if i>=K and t<P[i-K]+recurrent:return False
    return True

def legal_profile(P,d,profile,recurrent):
    K=len(profile)
    for i,t in enumerate(P):
        if i and t<P[i-1]+d[i]:return False
        if i<K and t<profile[i]:return False
        if i>=K and t<P[i-K]+recurrent:return False
    return True

def check():
    rng=Random(824275);n=0
    for h,K in product(range(1,11),(2,4,6)):
        for run in range(25):
            d=tuple(rng.randrange(1,5) for _ in range(max(h,K)))
            b=rng.randrange(-6,0);W=rng.randrange(1,7)
            E=tuple(rng.randrange(-8,13) for _ in range(K))
            p=earliest(d,E,b,h)
            for j in range(h+1):
                for S in combinations(range(h),j):
                    assert legal(S,d,E,b,W)==legal_profile(S,d,p,W)
                    n+=1
    print(n,'whole trace checks agree with the exact clipped prefix profile')

if __name__=='__main__':check()
