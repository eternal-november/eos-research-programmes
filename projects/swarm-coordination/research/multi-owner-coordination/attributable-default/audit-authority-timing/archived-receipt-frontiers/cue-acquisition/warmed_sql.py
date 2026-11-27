from contextlib import closing
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import sqlite3

from probe_lookup import Q,opened,look,vm,NAMES
import archived_matcher as m

BATCH='''select r.intent,r.tick,r.payload,r.result
from receipt r join log l on l.tick=r.tick
where r.intent in (?,?,?) and r.payload=l.payload and r.result=l.result'''

def warmed(path):
    d=opened(path)
    d.execute('begin')
    d.execute('select name from sqlite_schema order by name').fetchall()
    d.execute(Q,('none',)).fetchall()
    d.execute(BATCH,('none','other-1','other-2')).fetchall()
    return d

def trial(root):
    m.native(root)
    _,tags=m.J.plan()
    K={x:f'run:{tags[x]}' for x in NAMES}
    with closing(opened(root/'writer.sqlite')) as d:
        R={x:d.execute(Q,(K[x],)).fetchone() for x in NAMES}
        assert all(R.values())
    def point(d):
        return look(d,K[NAMES[0]],R[NAMES[0]])
    def identify(d):
        for s in NAMES[:-1]:
            if look(d,K[s],R[s]):return s
        return NAMES[-1]
    def batch(d):
        rows=d.execute(BATCH,tuple(K.values())).fetchall()
        named=[n for k,*v in rows for n in NAMES if K[n]==k and tuple(v)==R[n]]
        assert len(named)==1
        return named[0]
    def count_role(path, order):
        result={}
        for method in order:
            with closing(warmed(path)) as d:
                outcome,cost=vm(d,lambda:method(d))
                result[method.__name__]=(outcome,cost)
        return result
    ans={}
    for name in NAMES:
        path=root/f'{name}-copy.sqlite'
        fw=count_role(path,(point,identify,batch))
        bw=count_role(path,(batch,identify,point))
        assert fw==bw
        assert fw['point'][0]==(name==NAMES[0])
        assert fw['identify'][0]==fw['batch'][0]==name
        ans[name]=fw
    return ans

if __name__=='__main__':
    with TemporaryDirectory() as root:
        print(json.dumps(dict(sqlite=sqlite3.sqlite_version,native=trial(Path(root))),
                         sort_keys=True))
