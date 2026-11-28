"""Proposed service-owned capture reservation: serial civil simulator only."""
from itertools import product
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
import sqlite3,sys,os

# The environment's qualified producer emits exactly one tuple at capture.
# These fixtures have one expected producer per named order.
def init(db):
    with sqlite3.connect(db) as c:
        c.executescript("""
          PRAGMA journal_mode=WAL;
          CREATE TABLE published(key TEXT PRIMARY KEY, producer INT, park INT, tick INT, payload INT, auth INT);
          CREATE TABLE duty(name TEXT PRIMARY KEY, producer INT, park INT, earliest INT);
          CREATE TABLE response(name TEXT PRIMARY KEY, key TEXT, park INT, tick INT, payload INT, auth INT);
          CREATE TABLE control(name TEXT PRIMARY KEY, mode INT, park INT, auth INT);
          INSERT INTO duty VALUES ('A', 5, 8, 10), ('B', 5, 8, 0);
          INSERT INTO control VALUES ('A', 1, 8, 0), ('B', 1, 8, 0);
        """)

def capture(db,key,producer,park,tick,payload,auth=0,authorized=True):
    with sqlite3.connect(db) as c:
        c.execute('BEGIN IMMEDIATE')
        current=c.execute("SELECT tick,auth FROM published WHERE key=?",(key,)).fetchone()
        # Adapter scope: accepts updates for a fixed station episode only;
        # older arrival cannot overwrite an already accepted newer capture.
        if authorized and producer==5 and park==8 and (current is None or (current[1],current[0]) < (auth,tick)):
            c.execute('INSERT OR REPLACE INTO published VALUES (?,?,?,?,?,?)',(key,producer,park,tick,payload,auth))

def set_control(db,mode,park):
    with sqlite3.connect(db) as c:
        c.execute("UPDATE control SET mode=?,park=?,auth=auth+1 WHERE name='A' AND (mode!=? OR park!=?)",(mode,park,mode,park))

def service(db,name,key,now,crash='none'):
    # SQLite owns the ledger and simulator-held sample; no claim that
    # a robot move or sensor exposure is inside the DB transaction.
    with sqlite3.connect(db,isolation_level=None) as c:
        c.execute('BEGIN IMMEDIATE')
        mode,station,auth=c.execute("SELECT mode,park,auth FROM control WHERE name=?",(name,)).fetchone()
        p,park,start=c.execute('SELECT producer,park,earliest FROM duty WHERE name=?',(name,)).fetchone()
        old=c.execute('SELECT key,park,tick,payload,auth FROM response WHERE name=?',(name,)).fetchone()
        if old:
            if old[0]!=key:return ('spent',)
            if not mode or station!=old[1] or old[4]!=auth or not 0<=now-old[2]<=4:return ('settled',)
            return ('ok',old[3])
        if not mode or station!=park:return ('defer',)
        sample=c.execute('SELECT producer,park,tick,payload,auth FROM published WHERE key=?',(name,)).fetchone()
        if not sample:return ('defer',)
        owner,epoch,t,y,capture_auth=sample
        if owner!=p or epoch!=park or capture_auth!=auth or t<start or not 0<=now-t<=4:return ('defer',)
        c.execute('INSERT INTO response VALUES (?,?,?,?,?,?)',(name,key,epoch,t,y,auth))
        if crash=='before':os._exit(31)
        c.commit()
        if crash=='after':os._exit(32)
        return ('ok',y)

def branches():
    n=0
    for good,early_bad,changed,deferred_mode,qualified,arrival_order in product(*[(False,True)]*6):
      with TemporaryDirectory() as t:
        db=Path(t)/'case.db'
        init(db)
        capture(db,'B',5,8,10,77)
        capture(db,'A',5,8,9,12)
        if early_bad:assert service(db,'A','q',10)==('defer',)
        if arrival_order and good:capture(db,'A',5,8,10,91)
        if good:capture(db,'A',5,8,11,92)
        if not arrival_order:capture(db,'A',5,8,10,91) if good else None
        # A large timestamp cannot substitute for matching station incarnation.
        capture(db,'A',5,9,12,999)
        capture(db,'A',6,8,12,999)
        capture(db,'A',5,8,12,999,authorized=False)
        set_control(db,int(not deferred_mode),9 if changed else 8)
        r=service(db,'A','q',12 if qualified else 16)
        assert r==(('ok',92) if good and not changed and not deferred_mode and qualified else ('defer',)),r
        # Independent B has retained the captured pose throughout.
        assert service(db,'B','b',13)==('ok',77)
        n+=1
    return n

def rebound():
    with TemporaryDirectory() as t:
        db=Path(t)/'case.db'
        init(db)
        capture(db,'A',5,8,10,101)
        assert service(db,'A','same',10)==('ok',101)
        set_control(db,0,8);set_control(db,1,8)
        capture(db,'A',5,8,12,202,auth=2)
        capture(db,'A',5,8,13,303,auth=0)
        assert service(db,'A','same',12)==('settled',)
        assert service(db,'A','new',12)==('spent',)
        assert sqlite3.connect(db).execute("SELECT payload FROM published WHERE key='A'").fetchone()==(202,)

def crash_matrix():
    n=0
    for stage,revoke,change,delay in product(('before','after'),(False,True),(False,True),(1,6)):
      with TemporaryDirectory() as t:
        db=Path(t)/'case.db'
        init(db);capture(db,'A',5,8,10,101)
        r=run([sys.executable,__file__,'child',str(db),stage])
        assert r.returncode=={'before':31,'after':32}[stage]
        set_control(db,int(not revoke),9 if change else 8)
        capture(db,'A',5,8,12,202)
        now=12+delay
        z=service(db,'A','same',now)
        if stage=='after':
            assert z==(('ok',101) if not revoke and not change and now-10<=4 else ('settled',))
            assert service(db,'A','other',now)==('spent',)
        else:
            assert z==(('ok',202) if not revoke and not change and delay<=4 else ('defer',))
        n+=1
    return n

if __name__=='__main__':
    if len(sys.argv)>1:
        assert sys.argv[1]=='child'
        service(sys.argv[2],'A','same',10,sys.argv[3])
        raise AssertionError('missing requested crash')
    rebound()
    print(f'{branches()} modeled capture and independent-duty cases; {crash_matrix()} actual service process exits')
