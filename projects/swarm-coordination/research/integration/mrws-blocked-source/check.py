"""Cross-check outcomes, physical traces, and blocked-source witnesses from raw events."""
from pathlib import Path
import json
import sys

layout=Path('simu/data/whouse7x11.txt').read_text().splitlines()[::-1]
shelves=[(x,y) for y,row in enumerate(layout) for x,c in enumerate(row) if c=='S']
start={f'robot{i}':p for i,p in enumerate((x,y) for y,row in enumerate(layout) for x,c in enumerate(row) if c=='R')}
order=[f'item{i}' for i in range(9,0,-1)]
def check(r,v):
    pos=start.copy(); dead=set(); settled=[]; raw=[]
    seen=set(); carried={a:[] for a in pos}; completion=[]
    pickups=0
    for t,e in r['events']:
        c=e['command'];a=e.get('objName')
        if c=='MOVEROBOT':
            nxt=e['posX'],e['posY']
            assert a not in dead and (t,a) not in seen and nxt not in pos.values()
            assert sum(abs(x-y) for x,y in zip(nxt,pos[a]))==1
            seen.add((t,a)); pos[a]=nxt
        elif c=='ROBOTFAULT':
            assert e['faultType']=='battery_critical' and a not in dead
            assert a in pos and carried[a]
            raw.append((t,a,pos[a]));dead.add(a)
        elif c=='ITEMGAINED':
            cls=e['itemName']
            if a in pos:
                assert a not in dead and pos[a]==shelves[int(cls[4:])]
                carried[a].append(cls)
                assert len(carried[a])<=3
                pickups+=bool(r['first'] and t>=r['first'][0])
            elif a.startswith('goal'):
                settled.append(cls)
            assert settled==order[:len(settled)]
        elif c=='CLEARINV' and a in pos:
            assert a not in dead
            carried[a].clear()
        elif c=='ORDERCOMPLETE':
            assert settled==order
            completion.append(t)
    assert settled==r['landed'] and len(completion)<=1
    assert completion==([r['finish']] if r['finish'] else [])
    assert len(seen)==r['moves'] and not r['reject']
    assert carried=={a:z['items'] for a,z in r['last'].items()}
    if r['arm']=='clean':
        assert not raw and r['finish']==41
        return
    assert [list(x[:2]) for x in raw]==[x for x in [r['first'],r['second']] if x]
    assert pickups==r['picks_after']
    if v==1: blocked=9
    elif r['lag']==1: blocked=5
    elif r['arm']=='discard' and r['lag']==4: blocked=3
    else: blocked=None
    if blocked is not None:
        cls=f'item{blocked}'; p=shelves[blocked]
        assert any(loc==p for _,_,loc in raw)
        assert cls not in settled
        assert all(cls not in carried[a] for a in pos if a not in dead)
        assert r['finish'] is None
    else:
        assert r['finish']=={('discard',None):93,('retain',None):70,('retain',4):81}[(r['arm'],r['lag'])]
    if v==2 and r['arm']=='retain' and r['lag']==4:
        assert (23,'robot1',(5,4)) in raw and r['picks_after']==6
for v,p in enumerate(sys.argv[1:],1):
    rows=json.loads(Path(p).read_text())
    assert len({(r['seed'],r['arm'],r['lag']) for r in rows})==112
    for r in rows:check(r,v)
print('224 traces checked: legal unit movement, ordered native settlement, exact blocked-source witnesses')
