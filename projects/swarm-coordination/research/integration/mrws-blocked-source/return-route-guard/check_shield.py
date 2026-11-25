from itertools import product
from pathlib import Path
import json, sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'notice-timing'))
from check import audit, shelf

rows=json.loads(Path(sys.argv[1]).read_text());old=json.loads(Path(sys.argv[2]).read_text())
key=lambda r:(r['arm'],r['lag'],*r['notice_delays'])
seen=0
for r in rows:
    audit(r)
    events=r['events'];prefix=set()
    for i,(t,e) in enumerate(events):
        if e['command']=='ITEMGAINED' and e['objName'].startswith('goal'):prefix.add(e['itemName'])
        if e['command']=='HOMEAUDIT':
            p=e['posX'],e['posY']
            assert p not in {shelf[x] for x in range(1,10) if f'item{x}' not in prefix}
            dt,prev=events[i-1]
            assert prev=={**e,'command':'MOVEROBOT'} and dt==t
            seen+=1
a={key(r):r for r in rows};b={key(r):r for r in old}
assert a.keys()==b.keys() and len(a)==111
for f,s in product((0,1),(0,1,2,4,None)):
    x=a['discard',4,f,s]; orig=b['discard',4,f,s]
    assert not orig['finish'] and audit(orig)['robot1'][1]==shelf[3]
    assert x['finish']==93+f and audit(x)['robot1'][1] not in shelf
    assert x['picks_after']==9 and x['moves']==93
    assert x['events']==a['discard',4,f,0]['events']
for x in a.values():
    if x['lag']==1:assert not x['finish']
assert len([x for x in a if a[x]['finish'] is not None and b[x]['finish'] is None])==10
assert not any(b[x]['finish'] is not None and a[x]['finish'] is None for x in a)
assert a['retain',4,0,0]['finish']==75 and not a['retain',4,0,None]['finish']
print(f'111 paired runs; {seen} actual home moves independently checked; 10 restored completions')
