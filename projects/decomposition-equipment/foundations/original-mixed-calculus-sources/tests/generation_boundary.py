"""Exact small checks; no sampling, no external dependencies."""
from functools import lru_cache
from itertools import product

@lru_cache(None)
def rc(n, r):
    if not r:
        return 0
    rectangles = []
    for xs in range(1, 1 << n):
        for ys in range(1, 1 << n):
            z = sum(1 << (i*n+j) for i in range(n) for j in range(n)
                    if xs >> i & 1 and ys >> j & 1)
            if z & r == z:
                rectangles.append(z)
    @lru_cache(None)
    def cover(left):
        if not left:
            return 0
        first = left & -left
        return 1 + min(cover(left & ~z) for z in rectangles if z & first)
    return cover(r)

def comp(n, p, q):
    return sum(1 << (i*n+k) for i in range(n) for k in range(n)
               if any((p >> (i*n+j) & 1) and (q >> (j*n+k) & 1)
                      for j in range(n)))

n = 2
checks = 0
for p, r, q in product(range(1 << (n*n)), repeat=3):
    assert rc(n, comp(n, comp(n,p,r),q)) <= rc(n,r)
    checks += 1
print('Composition triples checked:', checks)
checks = 0
maps = list(product(range(n), repeat=n))
for r in range(1 << (n*n)):
    for f,g in product(maps,repeat=2):
        pre = sum(1 << (i*n+j) for i in range(n) for j in range(n)
                  if r >> (f[i]*n+g[j]) & 1)
        assert rc(n,pre) <= rc(n,r)
        checks += 1
print('Restriction cases checked:', checks)
for n in range(5):
    diagonal = sum(1 << (i*n+i) for i in range(n))
    assert rc(n,diagonal) == n
print('Diagonal exact ranks checked: 0, 1, 2, 3, 4')
checks = 0
for b in range(1, 5):
    for e in range(b+1):
        for injection in product(range(b), repeat=e):
            if len(set(injection)) != e:
                continue
            restricted = [(i,x,j) for i in range(e) for x in range(b)
                          for j in range(e) if injection[i] == x == injection[j]]
            assert restricted == [(i,injection[i],i) for i in range(e)]
            checks += 1
print('Injective carrier restrictions checked:', checks)
print('PASS')

# Exhaust every 2x2 matrix with entries 0,1,2. A nonzero rank-one
# factorization can be normalized to factors <= max entry: both factors
# have a positive coordinate, bounding every coordinate of the other.
def mm(p,q):
    return tuple(tuple(sum(p[i][j]*q[j][k] for j in range(len(q)))
                       for k in range(len(q[0]))) for i in range(len(p)))
I = ((1,0),(0,1))
checked = 0
rank_counts = {0:0, 1:0, 2:0}
for entries in product(range(3), repeat=4):
    x = (entries[:2], entries[2:])
    witnesses = [(u,v) for u in product(range(3),repeat=2)
                 for v in product(range(3),repeat=2)
                 if tuple(u[i]*v[j] for i in range(2) for j in range(2)) == entries]
    rank = 0 if not any(entries) else (1 if witnesses else 2)
    assert mm(x,I) == x
    for u,v in witnesses:
        assert mm(tuple((i,) for i in u),(v,)) == x
    rank_counts[rank] += 1
    checked += 1
special = ((1,1),(1,2))
assert not any(tuple(u[i]*v[j] for i in range(2) for j in range(2)) == (1,1,1,2)
               for u in product(range(3),repeat=2) for v in product(range(3),repeat=2))
assert mm(special,I) == special
assert rc(2,15) == 1
print('Exact integer-factor ranks checked:', checked, rank_counts)
print('Witness multiplicity counterexample: Boolean rank 1; integer factor rank 2')
print('ALL PASS')
