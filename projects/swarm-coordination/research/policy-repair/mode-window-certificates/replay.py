from itertools import combinations
from random import Random

def common(histories, ids, n_modes):
    return {(mode,t) for mode in range(n_modes) for t in range(10)
            if all(histories[i][mode][0]<=t<=histories[i][mode][1] for i in ids)}

def certify(histories,n_modes):
    reject=set()
    for mode in range(n_modes):
        lo=max(range(len(histories)),key=lambda i:histories[i][mode][0])
        hi=min(range(len(histories)),key=lambda i:histories[i][mode][1])
        if histories[lo][mode][0]<=histories[hi][mode][1]:
            return (mode,histories[lo][mode][0]),None
        reject.update((lo,hi))
    return None,reject

rng=Random(20261125)
for q in range(6400):
    r=rng.randrange(1,9); n=rng.randrange(1,21)
    h=[[tuple(rng.randrange(10) for _ in range(2)) for _ in range(r)] for _ in range(n)]
    good,cert=certify(h,r)
    raw=common(h,range(n),r)
    if raw:assert good in raw and cert is None
    else:assert good is None and len(cert)<=2*r and not common(h,cert,r)

for r in range(1,17):
    h=[[((j,j) if m==k else (0,1)) for m in range(r)] for k in range(r) for j in (0,1)]
    assert not common(h,range(2*r),r)
    for omit in range(2*r):
        assert common(h,set(range(2*r))-{omit},r)
    if r>1:
        assert all(common(h,pair,r) for pair in combinations(range(2*r),2))
print("6400 scoped certificate agreement checks")
print("tight rejecting witness of size 2r verified for r=1..16")
print("every pair agrees for r>=2 although the full information class is impossible")
