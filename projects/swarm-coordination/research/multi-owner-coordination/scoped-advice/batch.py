from math import comb
from itertools import combinations

def subsets(mask):
    s=mask
    while True:
        yield s
        if not s:return
        s=(s-1)&mask

checks=0
for c in range(1,10):
    for m in range(c+1):
        all_residual=[sum(1<<i for i in x) for x in combinations(range(c),m)]
        for grant in subsets((1<<c)-1):
            t=grant.bit_count()
            profiles={s&grant for s in all_residual}
            count=sum(comb(t,i) for i in range(max(0,m-(c-t)),min(t,m)+1))
            assert len(profiles)==count
            checks+=1
print(checks,"new authority scopes agree with exact supplemental-profile count")
