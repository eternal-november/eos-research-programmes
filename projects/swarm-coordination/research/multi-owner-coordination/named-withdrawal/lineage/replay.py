"""Replay all two-event branchings and read granularities using pinned native step."""
from pathlib import Path
from itertools import product
import sys
import json
from source_adapter import adapt

run=adapt(Path(sys.argv[2]).resolve())
all_rows=[];snapshot=None;stale_wrong=0;ambiguity_checks=0
for count in range(3):
    facts=list(product((False,True),repeat=count))
    for events,p,due in product(facts,(0,1),(0,1)):
        target=p ^ (sum(events)%2)
        for mode,missing in [('local',None),('unchanged-version',None),('lineage',None),
                             ('stale-audit',None),*(('lineage',j) for j in range(count))]:
            obs,r=run(p,due,mode,events=events,omitted=missing)
            if snapshot is None:snapshot=obs
            assert obs==snapshot
            assert r['declared_events']==list(events)
            expect=[target] if mode=='local' or (mode=='unchanged-version' and count==0) or (mode=='lineage' and missing is None) else []
            assert r['pickup']==expect and r['pay_later']==(due in expect)
            if mode=='stale-audit':
                assert not r['pickup'] and r['proposed']==[p]
                assert r['inappropriate_proposal']==(target!=p)
                stale_wrong+=r['inappropriate_proposal']
            else:assert not r['inappropriate_proposal']
            if missing is not None:
                known={i:e for i,e in enumerate(events) if i!=missing}
                possible={p ^ (sum(alt)%2) for alt in facts if all(alt[i]==v for i,v in known.items())}
                assert possible=={0,1}
                ambiguity_checks+=1
            all_rows.append(r)
assert len(all_rows)==152 and stale_wrong==12 and ambiguity_checks==40
print(json.dumps(dict(rows=all_rows,shared_snapshot=snapshot,missing_ambiguous=ambiguity_checks,
                      stale_inappropriate_proposals=stale_wrong),sort_keys=True,separators=(',',':')))
