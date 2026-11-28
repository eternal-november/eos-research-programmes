from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run
from contextlib import closing
import sqlite3,sys,json
worker=Path(__file__).with_name('actuator.py')
def call(db,*args):
    p=run([sys.executable,str(worker),str(db),*map(str,args)],capture_output=True,text=True,timeout=5)
    assert not p.stderr,p
    return p.returncode,json.loads(p.stdout) if p.stdout else None

def scenario(gate,cut,mode):
    with TemporaryDirectory() as d:
        p=Path(d)/"durable.sqlite"
        with closing(sqlite3.connect(p)) as db:
            db.executescript("""
            CREATE TABLE Authority(gate INTEGER,owner INTEGER);
            CREATE TABLE Physical(gate INTEGER,clear INTEGER);
            CREATE TABLE Committed(key TEXT PRIMARY KEY,actor INTEGER,start INTEGER,end INTEGER,gate INTEGER);
            """)
            db.execute("INSERT INTO Authority VALUES (?,10)",(gate,))
            db.execute("INSERT INTO Physical VALUES (?,1)",(gate,))
            db.commit()
        first=1_000_000
        length=250_000
        assert call(p,'use','Q',10,first,length,mode,cut)==({'before':51,'after':52}[cut],None)
        assert call(p,'transfer',gate)==(44,None)
        vfirst=first+50000
        v=call(p,'use','V',11,vfirst,length,mode,'reply')
        q=call(p,'use','Q',10,vfirst,length,mode,'reply')
        if cut=='before':
            assert q==(0,['stale',None]) # old authority no effect, no false settlement
            assert v==(0,['install',['V',11,vfirst,vfirst+length-1]])
            return False,False
        assert q==(0,['historical',['Q',10,first,first+length-1]])
        if mode=="owner-only":assert v[1][0]=='install'
        else:
            assert v==(0,['busy',None])
            # The last tick is still occupied. A resource refusal does
            # not consume V's identity or steal the effect from Q.
            assert call(p,'use','V',11,first+length-1,length,mode,'reply')==(0,['busy',None])
            at=first+length
            assert call(p,'use','V',11,at,length,mode,'reply')==(0,['install',['V',11,at,at+length-1]])
        with closing(sqlite3.connect(p)) as db:
            q,v=db.execute("SELECT key,start,end FROM Committed ORDER BY key").fetchall()
            assert q==('Q',first,first+length-1) and v[0]=='V'
            overlap=q[2]>=v[1]
        return overlap,True
result={}
for mode in ('full','owner-only'):
    x=[scenario(gate,cut,mode) for gate,cut in product(range(2),('before','after'))]
    result[mode]=dict(trials=len(x),overlaps=sum(v for v,_ in x),old_exact=sum(v for _,v in x))
assert result['full']['overlaps']==0 and result['owner-only']['overlaps']==2
print(json.dumps(result,sort_keys=True))
