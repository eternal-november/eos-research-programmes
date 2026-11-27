"""Read-only named-receipt queries scoped to one SQLite snapshot."""
import sqlite3

NAMES=('acceptA','unloadA','acceptB')

def opened(path):
    return sqlite3.connect(path.resolve().as_uri()+'?mode=ro',uri=True)

def vm(d,fn):
    n=0
    def step():
        nonlocal n
        n+=1
        return 0
    d.set_progress_handler(step,1)
    try:
        value=fn()
    finally:
        d.set_progress_handler(None,0)
    return value,n

Q='''select r.tick,r.payload,r.result
from receipt r join log l on l.tick=r.tick
where r.intent=? and r.payload=l.payload and r.result=l.result'''

def look(d,key,expected):
    return d.execute(Q,(key,)).fetchone()==expected
