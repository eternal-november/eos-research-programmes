"""Finite cylinder/first-hit witnesses, not a proof of infinite extension."""
from fractions import Fraction as F
from itertools import product
import json
# A fair stop/continue row with an additional raw zero continuation.
rows={():F(1)}
first=[]
for n in range(1,9):
    nxt={}
    for h,p in rows.items():
        if 'T' in h:
            nxt[h+('pad',)]=p
        else:
            for outcome,q in [('T',F(1,2)),('C',F(1,2)),('Z',F(0))]:
                nxt[h+(outcome,)]=p*q
    for h,p in rows.items():
        assert sum((q for k,q in nxt.items() if k[:-1]==h),F(0))==p
    assert sum(nxt.values())==1
    first.append(sum((p for h,p in nxt.items() if h[-1]=='T' and 'T' not in h[:-1]),F(0)))
    assert first[-1]==F(1,2**n)
    active=sum((p for h,p in nxt.items() if 'T' not in h),F(0))
    assert active==1-sum(first)==F(1,2**n)
    assert any(p==0 for p in nxt.values())
    rows=nxt
# Finite coherent port orders are not constrained to append-only.
ports=[]
for n in range(20):
    old=ports[:]; ports.insert(0,n)
    assert [p for p in ports if p in old]==old
assert ports==list(reversed(range(20)))
print(json.dumps({'status':'passed','horizons':8,'last_raw_prefix_count':len(rows),
 'zero_prefixes':sum(p==0 for p in rows.values()),'port_insertions':20,
 'scope':'finite cylinder conservation, zero retention, first-hit complement and prepend order only'},indent=2))
