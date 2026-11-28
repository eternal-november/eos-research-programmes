from pathlib import Path
from itertools import product
from tempfile import TemporaryDirectory
from subprocess import run
import json, sqlite3, sys
import contextlib
parent=Path(sys.argv[1])
worker=Path(__file__).with_name('worker.py')
def invoke(db,*a):
    return run([sys.executable,str(worker),str(db),*map(str,a)],capture_output=True,
               text=True,timeout=5)
def conflict(x,y):return max(x[0],y[0])<=min(x[1],y[1])
def sweep(closed,body):
    events=[(t,i,k) for i,(a,b) in enumerate((closed,body)) for t,k in ((a,1),(b+1,-1))]
    active={}
    for t in sorted(set(e[0] for e in events)):
        for _,i,k in (e for e in events if e[0]==t):
            active[i]=active.get(i,0)+k
        if sum(active.values())==2:return True
    return False
def scenario(r,rule,cut,grant):
    out,back=map(tuple,r['hulls'])
    i0,i1=r['cores'][1]
    maint=out[1]+1000000
    intent=maint+2000000
    applied={"ontime":intent,"return":i0-50000,"edge":back[1]+1}[grant]
    length=250000
    assert applied>=intent and length<i1-i0 and applied+length-1<r['end']
    keys=('independent_maintenance','queued_switch')
    intentions=(maint,intent)
    assert all(not conflict((t,t+length-1),w) for t,w in product(intentions,(out,back)))
    assert not conflict((maint,maint+length-1),(applied,applied+length-1))
    with TemporaryDirectory() as scratch:
        p=Path(scratch)/'plant.sqlite'
        with contextlib.closing(sqlite3.connect(p)) as db:
            db.executescript('''
                CREATE TABLE Hold(start INTEGER NOT NULL,finish INTEGER NOT NULL);
                CREATE TABLE Pending(key TEXT PRIMARY KEY, nominal INTEGER NOT NULL,span INTEGER NOT NULL);
                CREATE TABLE Installed(key TEXT PRIMARY KEY, start INTEGER NOT NULL, finish INTEGER NOT NULL);
                CREATE TABLE Receipt(key TEXT PRIMARY KEY, at INTEGER NOT NULL,decision TEXT NOT NULL);
                CREATE TABLE Event(key TEXT NOT NULL,at INTEGER NOT NULL,decision TEXT NOT NULL);
            ''')
            db.executemany('INSERT INTO Hold VALUES (?,?)',[out,back])
            db.commit()
        for key,t in zip(keys,intentions):
            p0=invoke(p,'issue',key,t,length)
            assert p0.returncode==43 and not p0.stderr and not p0.stdout
        p1=invoke(p,'apply',keys[0],maint,rule,'reply')
        assert (p1.returncode,p1.stdout,p1.stderr)==(0,'closed\n','')
        p2=invoke(p,'apply',keys[1],applied,rule,cut)
        assert p2.returncode=={'before':51,'after':52}[cut] and not p2.stdout and not p2.stderr
        p3=invoke(p,'apply',keys[1],applied,rule,'reply')
        assert p3.returncode==0 and not p3.stderr
        with contextlib.closing(sqlite3.connect(p)) as db:
            rows=db.execute('SELECT key,start,finish FROM Installed ORDER BY start').fetchall()
            rec=db.execute('SELECT key,at,decision FROM Receipt ORDER BY at').fetchall()
            ev=db.execute('SELECT key,at,decision FROM Event ORDER BY at').fetchall()
        assert ev==rec and len(rec)==2 and rec[1][2]==p3.stdout.strip()
        by_key={key:(a,b) for key,a,b in rows}
        assert by_key.get(keys[0])==(maint,maint+length-1)
        unsafe=any(sweep(a,b) for a,b in product(by_key.values(),(out,back)))
        assert unsafe==any(conflict(a,b) for a,b in product(by_key.values(),(out,back)))
        if unsafe:
            assert conflict(by_key[keys[1]],(i0,i1)) # guaranteed collision, not rounding band
        event=(applied,applied+length-1)
        direct_allow=not any(sweep(event,x) for x in (out,back))
        if rule=='effect':assert direct_allow==(keys[1] in by_key)
        return unsafe,int(keys[1] in by_key)
rules=('issued','intent','volatile','effect')
counts={k:[0,0,0] for k in rules}
for line in (parent/'PORTAL.jsonl').read_text().splitlines():
    r=json.loads(line)
    for rule,cut,grant in product(rules,('before','after'),('ontime','return','edge')):
        bad,admit=scenario(r,rule,cut,grant)
        u=counts[rule];u[0]+=1;u[1]+=bad;u[2]+=admit
assert counts==dict(issued=[12,4,12],intent=[12,4,12],volatile=[12,4,12],effect=[12,0,8])
print(json.dumps(counts,sort_keys=True))
