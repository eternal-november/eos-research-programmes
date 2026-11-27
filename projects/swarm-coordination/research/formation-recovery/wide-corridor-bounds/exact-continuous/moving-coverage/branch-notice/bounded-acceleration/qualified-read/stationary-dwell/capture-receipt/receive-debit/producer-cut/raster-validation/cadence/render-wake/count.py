from fractions import Fraction as F
from itertools import combinations

def count(wakes,due,period):
    # Nested time-neighborhood matching cut: k early slots plus late wakes.
    return min(k+sum(w>=due+k*period for w in wakes) for k in range(len(wakes)+1))

def actual(wakes,due,p):
    n=0
    for w in wakes:
        if w>=due+n*p:
            n+=1
    return n

def exact_match(wakes,due,p,n):
    return any(all(w>=due+j*p for j,w in enumerate(c)) for c in combinations(wakes,n))

nt=0
for mask in range(1<<10):
    wakes=[t for t in range(10) if (mask>>t)&1]
    for d in range(-4,12):
        for p in range(1,6):
            n=count(wakes,d,p)
            assert n==actual(wakes,d,p)
            if len(wakes)<=6:
                assert exact_match(wakes,d,p,n) and not exact_match(wakes,d,p,n+1)
            nt+=1
print(f'{nt} masked-window count checks')
# Qualified aperture transplanted from the exact far-site model in #770.
sigma=F(400,637)
delta=7-F(637,100)-sigma
eps=F(1,1000)
decode=F(105,1000)
assert eps + 10*(decode-F(1,10))**2 <= delta < F(3,1000)
# q is 10 ms from fixture origin. A prior fire moves next-due from
# 2 ms to 52 ms in the relative fixture clock, hence outside the aperture.
for due_b in [False,True]:
    for due_c in [False,True]:
        wakes=([9] if due_c else [])+([11] if due_b else [])
        assert bool(count(wakes,2,50)-count([t for t in wakes if t<10],2,50))==(due_b and not due_c)
assert 52-10>delta*1000
print('Exact far-site timing: q+1 ms with 105 ms decode passes; q+42 ms is too late')
