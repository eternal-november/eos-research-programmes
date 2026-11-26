#!/usr/bin/env python3
"""Use separated pinned fixtures; couple their old scopes by a declared model."""
import contextlib
import io
import json
import sys
from itertools import product
from pathlib import Path

scope=Path(sys.argv[1]).resolve()
up=Path(sys.argv[2]).resolve()
driver=Path(sys.argv[3]).resolve()
sys.path.insert(0,str(scope))
sys.argv=[str(scope/'scope_replay.py'),str(up),str(driver)]
with contextlib.redirect_stdout(io.StringIO()) as captured:
    import scope_replay as p
assert json.loads(captured.getvalue())['native_runs_per_backend']==36

from replay import direct,ordered_pair

rows=[]
masks=[]
# Sites 0,1 are warehouse L,R, while 2,3 are radio L,R.
# All four independent combinations are replayed. One is excluded only
# by the declared coupled source law, not by either upstream simulator.
for left_old,right_old in product('LR',repeat=2):
    pairs=[]
    for x,y in product('LR',repeat=2):
        wx=p.one(p.WScope,left_old,left_old,False,lambda _:x)
        ry=p.one(p.NScope,right_old,right_old,False,lambda _:y)
        assert wx[1:]==ry[1:]==(1,1,1)
        if wx[0] and ry[0]:
            pairs.append(x+y)
    assert len(pairs)==1
    x,y=pairs[0]
    m=(1<<'LR'.index(x)) | (1<<(2+'LR'.index(y)))
    rows.append(dict(old=[left_old,right_old],allowed_pair=x+y))
    masks.append(m)

coupled=sorted(x for x in masks if x!=6)  # exclude warehouse R and radio L
assert coupled==[5,9,10]
assert direct(coupled,2)==ordered_pair(coupled,4)==3
assert direct(masks,2)==ordered_pair(masks,4)==4
print(json.dumps(dict(source_rows=rows,declared_coupled_support=coupled,
                      coupled_adaptive_cost=3,coupled_fixed_order_cost=4,
                      complete_product_adaptive_cost=4),indent=2))
