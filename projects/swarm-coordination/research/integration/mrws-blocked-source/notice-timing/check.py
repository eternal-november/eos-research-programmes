"""Audit the frozen notice family from raw events and verify the original replay."""
from itertools import product
from collections import Counter
from pathlib import Path
import hashlib, json, sys

layout=Path("simu/data/whouse7x11.txt").read_text().splitlines()[::-1]
shelf=[(x,y) for y,r in enumerate(layout) for x,c in enumerate(r) if c=="S"]
start={f"robot{i}":(x,y) for i,(x,y) in enumerate(
    (x,y) for y,r in enumerate(layout) for x,c in enumerate(r) if c=="R")}
need=[f"item{i}" for i in range(9,0,-1)]

def audit(row):
    p=start.copy(); halt={}; got=[]; count=0; moves=set(); notices={}
    for t,a in row['notices']:
        assert a not in notices
        notices[a]=t
    for t,x in row['events']:
        a=x.get('objName'); c=x['command']
        if c=='ROBOTFAULT':
            assert a not in halt and x['faultType']=='battery_critical'
            halt[a]=(t,p[a])
        elif c=='MOVEROBOT':
            pos=x['posX'],x['posY']
            assert a not in halt and pos not in p.values() and (t,a) not in moves
            assert abs(pos[0]-p[a][0])+abs(pos[1]-p[a][1])==1
            p[a]=pos;moves.add((t,a))
        elif c=='ITEMGAINED' and a.startswith('robot'):
            assert a not in halt and p[a]==shelf[int(x['itemName'][4:])]
        elif c=='ITEMGAINED' and a.startswith('goal'):
            got.append(x['itemName'])
            assert got==need[:len(got)]
        elif c=='ORDERCOMPLETE':
            assert len(got)==len(need) and t==row['finish']
            count+=1
    assert count==int(row['finish'] is not None) and not row['reject']
    assert got==row['landed'] and len(moves)==row['moves']
    assert all(a in halt and t>=halt[a][0] for a,t in notices.items())
    if not notices:
        assert all('robot3' not in who for _,who in row['assigned_trace'])
    return halt

def main(rows,old,expected):
    r={(x['arm'],x['lag'],*x['notice_delays']):x for x in rows}
    assert len(r)==111
    c0={(x['arm'],x['lag']):x for x in old if x['seed']==0}
    for k,x in r.items():
        audit(x)
        if k[-2:]==(0,0):
            assert {f:v for f,v in x.items() if f not in {'notice_delays','notices','assigned_trace'}}==c0[k[:2]]
    def blocked(k,item):
        x=r[k]; h=audit(x)
        assert x['finish'] is None and x['last']['robot3']['target']==f'shelf{item}'
        assert h['robot1'][1]==shelf[item]
        assert f'item{item}' not in x['landed']
        assert all(f'item{item}' not in z['items'] for z in x['last'].values() if not z['dead'])
    for v in (0,1,2,4,None):
        blocked(('discard',4,0,v),3)
        blocked(('retain',4,2,v) if v is not None else ('discard',4,1,v),
                4 if v is not None else 3)
        assert r['discard',4,2,v]['finish']==101
        assert r['discard',4,2,v]['events']==r['discard',4,2,0]['events']
        assert r['discard',4,2,v]['repairs']==[[21,1,'native-discard']]
    assert audit(r['retain',4,0,None])['robot1'][1] not in shelf
    assert 'robot1' in r['retain',4,0,None]['assigned_trace'][-1][1]
    assert r['retain',4,0,None]['finish'] is None
    assert r['retain',4,0,0]['finish']==81
    assert all(r['retain',4,u,v]['finish']<=100 for u,v in product((0,1),(0,1,2,4)))
    assert all(r['retain',None,u,0]['finish']<=100 for u in (0,1))
    cs=Counter((x['arm'],x['lag'],x['result']) for x in rows)
    print('111 traces; 7 exact no-delay controls; compound plant-and-grant witnesses checked')
    print(sorted((a,str(b),s,n) for (a,b,s),n in cs.items()))

if __name__=='__main__':
    raw,ref,expected=map(Path,sys.argv[1:])
    assert hashlib.sha256(ref.read_bytes()).hexdigest()==expected.read_text().splitlines()[1].split()[0]
    main(json.loads(raw.read_text()),json.loads(ref.read_text()),expected)
