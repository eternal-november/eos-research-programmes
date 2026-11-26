"""Replay a later authorized designation after the old return and movement clear."""
from hashlib import sha1
from pathlib import Path
import json
import sys

base=Path(sys.argv[2]).resolve()
for name,digest in [('replay.py','6da73a9caf6a2c2a617f64c1a80c1f5a8d4b3aa9'),
                    ('control.py','2037bab075131b33a7b16ab67e49658bbad27e5e'),
                    ('fallback.py','f7ca58a140cce0c271012c31526e62379b2a304a')]:
    data=(base/name).read_bytes()
    assert sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==digest
sys.path.insert(0,str(base))
p=base/'replay.py'
source=p.read_text()
changes={
 'marker_tick=1,earlier_need=None):':'marker_tick=1,earlier_need=None,due_start=DUE+1):',
 'earlier_need!=blocked and marker_tick==2)':'earlier_need!=blocked and marker_tick>=2)',
 'assert marker_tick in (1,2)':'assert 1<=marker_tick<due_start',
 'range(1,DUE+3)':'range(1,due_start+2)',
 'if tick in (DUE+1,DUE+2):':'if tick in (due_start,due_start+1):',
 'assert tick==DUE+2':'assert tick==due_start+1',
 '            if tick==2 and earlier_need is not None:':'        if tick==marker_tick and earlier_need is not None:'
}
for old,new in changes.items():
    assert source.count(old)==1,(old,source.count(old))
    source=source.replace(old,new)
ns={'__name__':'inherited'}
exec(compile(source,str(p),'exec'),ns)
def run():
    outcomes=[]
    for b in ns['BAYS']:
        for q in ns['BAYS']:
            if q==b:continue
            first=ns['choose'](b,q)
            marker=7
            bad,view=ns['run'](b,q,'fallback',cut=1,marker_tick=marker,
                               earlier_need=first,due_start=8)
            good,view0=ns['run'](b,q,'fixed',fixed=first,marker_tick=marker,
                                 earlier_need=first,due_start=8)
            stable=ns['run'](b,first,'fallback',cut=1,marker_tick=1,due_start=8)
            # Early report is the first branch in both causal worlds of this
            # witness. The positive fixed-site control has the same final job
            # and resources as the reassigning failure, not an easier deadline.
            assert view==view0==[ns['NAMES'][first]]*2
            assert bad[0]+1<marker and good[0]+1<marker
            assert not bad[1] and good[1] and stable[1]
            assert bad[0]==stable[0] and bad[2]==good[2]==stable[2]==1
            outcomes.append(dict(blocked=ns['NAMES'][b],early_ingress=ns['NAMES'][first],
                  later_chooses=ns['NAMES'][q],native_reassign_at=marker,
                  due=9,unchanged_receiver=bad,fixed_site_control=good,
                  stable_designation_control=stable))
    assert len(outcomes)==6
    return outcomes

if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
