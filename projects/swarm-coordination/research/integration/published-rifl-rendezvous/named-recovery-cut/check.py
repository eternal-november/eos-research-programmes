#!/usr/bin/env python3
from itertools import product
import json

def envelope(n, allowed, checked):
    """Bit masks for copy-holder sets; checked nodes had qualified negative reads."""
    possible=[s for s in allowed if (s & checked)==0]
    return not possible

n=4
counts=0
for f in range(1,1<<((1<<n)-1)):
    copies=[s for s in range(1,1<<n) if f>>(s-1)&1]
    for cleared in range(1<<n):
        # Direct distinguishability: in each fixture, copies can jointly
        # match absence exactly on the queried projection or not.
        answer={s!=0 for s in [0]+copies if all(
            not (s>>i&1) for i in range(n) if cleared>>i&1)}
        hit=all(s&cleared for s in copies)
        assert hit==envelope(n,copies,cleared)==(answer=={False})
        counts+=1

pair_quorum=(3,5,6)
assert min(c.bit_count() for c in range(8) if envelope(3,pair_quorum,c))==2
singleton_after_second_fault=(1,2,4)
assert min(c.bit_count() for c in range(8) if envelope(3,singleton_after_second_fault,c))==3
assert envelope(3,pair_quorum,3) and not envelope(3,singleton_after_second_fault,3)
# Same two negative replies: empty model or the old exact record surviving
# only at C once the earlier two-copy write guarantee no longer transports.
assert [s for s in (0,4) if s&3==0]==[0,4]
# Reading A while record is on B, then B after transfer to A.
assert (2&1,1&2)==(0,0) and all((s&3)!=0 for s in (2,1))

print(json.dumps({"families":(1<<15)-1,"negative_projections":counts,
                  "pair_quorum_reads":2,"split_recovery_reads":3},sort_keys=True))
