"""Independent report-row permutation regression; finite sanity check only."""
import sys, random
from binding_checker import check, verify_positive
rng=random.Random(431)
for trial in range(2000):
    n=rng.randrange(1,10)
    edges=[[j for j in range(n) if rng.random()<.5] for i in range(n)]
    roles=[rng.randrange(3) for i in range(n)]
    bits=[rng.randrange(2) for j in range(n)]
    a=check(edges,roles,bits)
    perm=list(range(n)); rng.shuffle(perm)
    inv={v:j for j,v in enumerate(perm)}
    e2=[[inv[j] for j in row] for row in edges]
    b2=[bits[j] for j in perm]
    b=check(e2,roles,b2)
    assert a['status']==b['status']
    if a['status']=='CERTIFIED':
        assert a['parity_mask']==b['parity_mask']
        assert verify_positive(e2,roles,b2,b)
print('PASS: 2000 independent report-row permutation invariance cases.')
