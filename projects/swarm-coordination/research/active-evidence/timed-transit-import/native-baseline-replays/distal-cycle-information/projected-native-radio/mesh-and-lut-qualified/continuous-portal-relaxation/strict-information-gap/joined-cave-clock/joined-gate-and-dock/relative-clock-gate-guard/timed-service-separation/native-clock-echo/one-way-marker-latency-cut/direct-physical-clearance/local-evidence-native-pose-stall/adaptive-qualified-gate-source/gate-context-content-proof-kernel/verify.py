"""Compare the specified composite transition to the real SQLite worker."""
from itertools import permutations
from pathlib import Path
from tempfile import TemporaryDirectory
from contextlib import closing
from subprocess import run
import json,sqlite3,sys
from kernel import run as expected

WORK=Path(__file__).with_name('native.py')
def invoke(db,cmd):
    p=run([sys.executable,str(WORK),str(db),*map(str,cmd)],check=False,
      capture_output=True,text=True,timeout=5)
    assert not p.stderr, (cmd,p.stderr)
    return p.returncode,p.stdout.strip()
def actual(sequence):
    with TemporaryDirectory() as d:
        p=Path(d)/'gate.sqlite'
        with closing(sqlite3.connect(p)) as db:
            db.executescript("""
            CREATE TABLE Hold(start INTEGER,finish INTEGER);
            CREATE TABLE Pending(key TEXT PRIMARY KEY,nominal INTEGER,span INTEGER);
            CREATE TABLE Installed(key TEXT PRIMARY KEY,start INTEGER,finish INTEGER);
            CREATE TABLE Receipt(key TEXT PRIMARY KEY,at INTEGER,decision TEXT);
            CREATE TABLE Event(key TEXT PRIMARY KEY,at INTEGER,decision TEXT);
            CREATE TABLE ExitReceipt(gate INTEGER,era INTEGER,mission TEXT);
            CREATE TABLE Authority(gate INTEGER,era INTEGER);
            CREATE TABLE Owner(holder INTEGER);
            CREATE TABLE QueuedOwner(key TEXT PRIMARY KEY,old_owner INTEGER);
            CREATE TABLE AuthChange(key TEXT PRIMARY KEY,prior INTEGER,next INTEGER,at INTEGER);
            CREATE TABLE Denied(key TEXT,principal INTEGER,holder INTEGER,PRIMARY KEY(key,principal,holder));
            CREATE TABLE EffectAuthority(key TEXT PRIMARY KEY,principal INTEGER,holder INTEGER);
            CREATE TABLE SourceReceipt(source INTEGER PRIMARY KEY);
            INSERT INTO Authority VALUES(0,7);
            INSERT INTO Owner VALUES(10);
            INSERT INTO QueuedOwner VALUES('Q',10);
            """)
        assert invoke(p,('issue','Q',0,7))==(43,'')
        def read(db):
            row=db.execute("SELECT decision,at FROM Receipt WHERE key='Q'").fetchone()
            act=db.execute("SELECT principal,holder FROM EffectAuthority WHERE key='Q'").fetchone()
            assert act is None or act[0]==act[1]
            assert (row is not None and row[0]=='closed')==(act is not None)
            return None if row is None else (row[0],row[1],0 if act is None else act[0])
        ans=[]
        for t,(k,v) in enumerate(sequence,1):
            if k=='attest':
                with closing(sqlite3.connect(p)) as db:
                    db.execute("INSERT OR IGNORE INTO ExitReceipt SELECT 0,7,'return' WHERE NOT EXISTS (SELECT 1 FROM ExitReceipt)")
                    db.execute("INSERT OR IGNORE INTO SourceReceipt VALUES(?)",(v,))
                    db.commit()
                ans.append(('recorded',))
            elif k=='handoff':
                assert invoke(p,('transfer','A',10,v,t))==(44,'')
                r=invoke(p,('transfer','A',10,v,t))
                assert r==(0,'transferred')
                ans.append(('transferred',))
            elif k=='inspect':
                with closing(sqlite3.connect(p)) as db:ans.append(('historical',read(db)))
            else:
                with closing(sqlite3.connect(p)) as db:pre=read(db)
                rc,o=invoke(p,('apply','Q',t,'clearance','reply',v))
                assert rc==0
                with closing(sqlite3.connect(p)) as db:post=read(db)
                if pre is not None:
                    assert post==pre and post[0]==o
                    ans.append(('historical',post))
                elif o=='stale':
                    assert post is None
                    ans.append(('stale',))
                else:
                    assert post is not None and post[0]==o
                    ans.append(('fresh',post))
        with closing(sqlite3.connect(p)) as db:
            holder,=db.execute("SELECT holder FROM Owner").fetchone()
            mask=sum(x for x, in db.execute("SELECT source FROM SourceReceipt"))
            final=read(db)
            inst=db.execute("SELECT start,finish FROM Installed WHERE key='Q'").fetchall()
            assert inst==([] if final is None or final[0]!='closed' else [(final[1],final[1]+6)])
        return (holder,mask,final),ans
counts={}
for owner in (0,11):
    k=0
    for w in permutations([('attest',1),('attest',2),('handoff',owner),('apply',10),('apply',11)]):
        word=w[:3]+(('inspect',10),)+w[3:]+(('inspect',11),)
        s,r=expected(word)
        assert actual(word)==((s.law.holder,s.facts.witnesses,s.facts.receipt),r)
        k+=1
    counts[owner]=k
print(json.dumps(counts,sort_keys=True))
