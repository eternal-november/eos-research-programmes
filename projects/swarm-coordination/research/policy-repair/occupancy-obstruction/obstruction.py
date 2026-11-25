"""Irredundant exclusion witnesses for a common live-inspection launch."""
from itertools import combinations, product
from random import Random

def min_horizon(k,w):
    assert k>=1 and w>=1
    if k==1:return 1
    j,r=divmod(k,2)
    return (j-1)*(w+1)+2 if r==0 else j*(w+1)+1

def maximum(n,w):
    q,r=divmod(n-1,w+1)
    return 2*q+int(r!=0)+1

def build(n,w,k):
    assert min_horizon(k,w)<=n<=k*w
    if k==1: return (0,)
    starts=[0]
    for i in range(1,k):
        starts.append(starts[-1]+(w if i%2==1 else 1))
    l=w-1
    right=starts[-2]+w
    while right-l+1<n and l>0:
        l-=1
    while right-l+1<n and right<starts[-1]+w-1:
        right+=1
    for i in range(1,k):
        while right-l+1<n and starts[i]-starts[i-1]<w:
            starts[i:]=[s+1 for s in starts[i:]]
            right+=1
    assert right-l+1==n
    return tuple(x-l for x in starts)

def mask(n,s,w):
    return sum(1<<t for t in range(max(0,s),min(n,s+w)))

def irredundant(n,ivs):
    full=(1<<n)-1
    masks=[mask(n,*iv) for iv in ivs]
    seen=0; multi=0
    for m in masks:
        multi|=seen&m;seen|=m
    return seen==full and all(m&~multi for m in masks)

def smallest_cover(n,ivs):
    # ordinary interval-cover greedy, with stable source IDs, not a matching
    # or a search over amended permissions.
    unc=0; ids=[]
    while unc<n:
        covering=[(s+w,i) for i,(s,w) in enumerate(ivs) if s<=unc<s+w]
        if not covering:
            return None
        unc,i=max(covering)
        ids.append(i)
    return ids

def native(n,old_holds,own_dwell):
    return [t for t in range(n)
            if all(t+own_dwell<=s or s+h<=t for s,h in old_holds)]

def main():
    m=0
    for n,w in product(range(1,13),range(1,6)):
        mk=0
        for k in range(1,n+1):
            for ss in combinations(range(1-w,n),k):
                if irredundant(n,tuple((s,w) for s in ss)):mk=k
                m+=1
        assert mk==maximum(n,w),(n,w,mk,maximum(n,w))
    print(m,'exhaustive equal-width candidate families')
    for n,w in product(range(1,151),range(1,26)):
        k=maximum(n,w)
        assert k*w>=n
        assert min_horizon(k+1,w)>n
        assert min_horizon(k,w)<=n
        ivs=[(s,w) for s in build(n,w,k)]
        assert irredundant(n,ivs)
        assert len(smallest_cover(n,ivs))==k
    print('3750 exact sharp constructed extremes')
    rng=Random(742421)
    for i in range(4000):
        n=rng.randrange(1,10); d=rng.randrange(1,6)
        h=rng.randrange(1,5)
        holds=[(rng.randrange(-5,14),rng.randrange(h,h+6)) for _ in range(rng.randrange(9))]
        ivs=[(s-d+1,hw+d-1) for s,hw in holds]
        cs=smallest_cover(n,ivs)
        assert (cs is not None)==(not native(n,holds,d))
        if cs is not None:
            for k in range(len(cs)):
                assert not any(irredundant(n,ps) for ps in combinations(ivs,k))
            assert len(cs)<=maximum(n,d+h-1)
    print('4000 actual half-open occupancy/variable-width/greedy checks')
if __name__=='__main__':main()
