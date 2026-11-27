"""Compare holder-restricted read-only and current-supplier confirmation."""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import tempfile
import joined

def test(out,source,copy,fail,erase,form,notice,work,readonly):
    actual,held,closed,result=out
    assert held=={"P":int(actual),"Q":int(actual and copy and not erase),
                 "stage_bytes":int(actual)*(2+2*copy)}
    assert actual==(source=="exact") and closed["other_delta"]==1 and result["other"]==1
    assert result["older"]==(work!="off")
    holders=[s for s,v in (("P",held["P"] and not fail),("Q",held["Q"])) if v]
    selected="Q" if fail else "P"
    if not readonly:holders=[s for s in holders if notice and s==selected]
    size=3 if form=="full" else 2
    rx=3 if not readonly and notice else 0
    raw=0
    for s in holders:
        if s=="Q" and work=="late":continue
        if rx+size<=5:
            rx+=size;raw+=1
    assert result["tries"]==len(holders) and result["rx"]==rx and result["raw"]==raw
    assert result["receipt"]==(5 if raw and form!="stale" else -1)
    assert result["egress"]==(8 if raw and form!="stale" else 9)

sum_=Counter();witness={}
for source,copy,fail,erase,form,notice,work,read in product(
    ("exact","sibling"),(False,True),(False,True),(False,True),
    ("short","full","stale"),(False,True),("off","early","late"),(False,True)):
    mode=("read-" if read else "")+form
    with tempfile.TemporaryDirectory() as d:
        out=joined.execute(Path(d)/"a.db",source,copy,fail,erase,mode,notice,work)
    test(out,source,copy,fail,erase,form,notice,work,read)
    result=out[-1]
    sum_.update(cases=1,qualified=int(result["receipt"]>=0))
    if source=="exact" and copy and not erase and work=="off" and form!="stale":
        name=f"{'read' if read else 'role'}/{form}/{'lost' if fail else 'live'}/{'loud' if notice else 'mute'}"
        witness[name]=result
assert witness["read/short/lost/mute"]["egress"]==8
assert witness["role/short/lost/mute"]["egress"]==9
assert witness["role/short/live/loud"]["rx"]==5
assert witness["read/short/live/loud"]["rx"]==4
assert witness["read/full/lost/mute"]["egress"]==8
print(json.dumps({"summary":sum_,"representative":witness},sort_keys=True))
