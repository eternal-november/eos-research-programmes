#!/usr/bin/env python3
"""Read availability from the pinned existing held-scope adapter, by action replay."""
import contextlib
import io
import json
import sys
from pathlib import Path

scope=Path(sys.argv[1]).resolve()
up=Path(sys.argv[2]).resolve()
driver=Path(sys.argv[3]).resolve()
sys.path.insert(0,str(scope))
sys.argv=[str(scope/'scope_replay.py'),str(up),str(driver)]
with contextlib.redirect_stdout(io.StringIO()) as captured:
    import scope_replay as pair
original=json.loads(captured.getvalue())
assert original['native_runs_per_backend']==36

from replay import game,optimal

out={}
for adapter in (pair.WScope,pair.NScope):
    supports=[]
    for old in 'LR':
        mask=0
        for i,site in enumerate('LR'):
            # Source execution on a clean copy for each possible rescue. No
            # test changes the pending old scope after the cut.
            row=pair.one(adapter,old,old,False,lambda _:site)
            success,unrelated,old_progress,old_still_owed=row
            assert unrelated==old_progress==old_still_owed==1
            mask|=success<<i
        supports.append(mask)
    left=game(supports,3,[1,1],True)
    right=game(supports,3,[1,1],False)
    assert left==optimal(supports,3,[1,1],True)==1
    assert right==optimal(supports,3,[1,1],False)==2
    out[adapter.__name__]=dict(masks=supports,inference=left,verified=right)
print(json.dumps(out,indent=2))
