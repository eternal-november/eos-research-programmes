#!/usr/bin/env python3
from itertools import product
import json,sys
from collections import Counter
ranges=list(product(range(-6,7),range(-3,4),range(6),range(1,4),range(-6,7),range(3)))
rows={}
tallies=Counter()
for line in open(sys.argv[1],encoding="utf-8"):
    p,v,b,r,d,m,w,c=map(int,line.split())
    assert (p,v,b,r,d,m) not in rows
    rows[p,v,b,r,d,m]=w,c
    h=(p,v,d)[m]
    valid=[a for a in range(-8,b+1) if abs(a-h)<=r]
    if valid:
        expected=min(valid,key=lambda a:abs(a-d))
        assert w==expected and c==(w!=d)
        tallies["nonempty"]+=1
    else:
        assert h-r>b # Lower-side conflict impossible in the chosen ranges.
        assert w==min(max(d,b),h-r) and c==(w!=d)
        assert not (-8<=w<=b and abs(w-h)<=r)
        if c==0:tallies["empty_unchanged"]+=1
        if w>b and abs(w-h)>r:tallies["fails_both"]+=1
        tallies["empty"]+=1
assert set(rows)==set(ranges)
assert rows[4,0,1,1,2,0]==(2,0)
assert rows[4,0,1,1,2,1]==(1,1)
assert rows[4,0,1,1,4,2]==(3,1)
max_steps=0
for p,b,r in product(range(-6,7),range(6),range(1,4)):
    # Prepare under the previous range. Distinct integers make this
    # an independent shortest-path check rather than a clamp replay.
    k=min((s for s in range(10) if max(0,p-b)<=(s+1)*r))
    reached={p}
    for step in range(10):
        if any(abs(v-u)<=r for v in reached for u in range(-8,b+1)):
            assert step==k
            break
        reached={z for z in range(-8,9) if any(abs(z-v)<=r for v in reached)}
    else:raise AssertionError()
    max_steps=max(max_steps,k)
print(json.dumps({"native_rows":len(rows),**tallies,
                  "preparation_cases":13*6*3,"largest_preparation_cycles":max_steps},sort_keys=True))
