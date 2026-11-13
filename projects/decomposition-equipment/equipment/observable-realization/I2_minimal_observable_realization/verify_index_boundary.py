#!/usr/bin/env python3
"""Independent finite arithmetic checks, not an unbounded theorem prover."""
import itertools, json
from pathlib import Path

def compositions(n,m):
    if m==1:
        yield (n,)
    else:
        for a in range(n+1):
            for tail in compositions(n-a,m-1):
                yield (a,)+tail
checks=0
for n in range(11):
    for m in range(1,8):
        tuples=list(compositions(n,m))
        assert all(sum(x)==n for x in tuples)
        assert any(all(a>0 for a in x) for x in tuples)==(n>=m)
        checks+=1
for t in range(2,9):
    mul=lambda a,b:min(t,a+b)
    for a,b,c in itertools.product(range(t+1),repeat=3):
        assert mul(mul(a,b),c)==mul(a,mul(b,c))
        assert (mul(a,b)==0)==(a==0 and b==0)
        checks+=1
    # Enumerate sets of achievable positive factor sums via independent DP.
    positive_sums={0}
    truths=[[] for _ in range(t+1)]
    for m in range(1,t+4):
        positive_sums={mul(a,b) for a in positive_sums for b in range(1,t+1)}
        for n in range(t+1):
            result=n in positive_sums
            assert result==(n==t or m<=n)
            truths[n].append(result)
            checks+=1
    assert len({tuple(v) for v in truths})==t+1
    # Exact signature image is source-dependent, despite graft homomorphism.
    q=lambda n:min(t,n)
    image_t={(q(a),q(b)) for a,b in compositions(t,2)}
    image_next={(q(a),q(b)) for a,b in compositions(t+1,2)}
    abstract={(a,b) for a,b in itertools.product(range(t+1),repeat=2) if mul(a,b)==t}
    assert (t,1) in abstract and (t,1) not in image_t and (t,1) in image_next
    assert image_t!=image_next
    for a,b in itertools.product(range(2*t+2),repeat=2):
        assert q(a+b)==mul(q(a),q(b))
        checks+=1
result={'status':'PASS','checks':checks,'ordinary_n_range':[0,10], 'ordinary_m_range':[1,7], 'capped_t_range':[2,8], 'capped_m_range':'1 through t+3','unbounded_proof':'index_boundary_theorem.md','claims_excluded':['general finite-index decidability','capped monoid as exact-may quotient of N','bounded checks as unbounded proof']}
Path(__file__).with_name('index_boundary_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
