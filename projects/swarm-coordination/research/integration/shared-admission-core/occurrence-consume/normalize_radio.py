"""Use native station state to qualify previously replayed native radio tapes."""
import json,subprocess,sqlite3,types,sys
from contextlib import closing
from pathlib import Path
from tempfile import TemporaryDirectory
from fractions import Fraction as F
from consume import Event,Contract,first
from radio_trace import parse

def read_owner(up):
    p=up/'owner.py'
    s=p.read_text()
    marker='\nif len(sys.argv)>2 and sys.argv[2]=="fencer":'
    assert s.count(marker)==1
    ns=types.ModuleType('owner')
    ns.__file__=str(p)
    exec(compile(s.split(marker)[0],str(p),'exec'),ns.__dict__)
    return ns

def go(station,case,root):
    old,new=root/'old.sqlite',root/'new.sqlite'
    station.init(old,True)
    assert station.run(old,1,'after-commit',True)=={'status':'silent'}
    if case['stale']:
        station.transfer(old,new)
    digest=station.fence(old)
    if not case['stale']:
        station.transfer(old,new)
    with closing(sqlite3.connect(new.resolve().as_uri()+'?mode=ro',uri=True)) as db:
        db.execute('begin')
        right=db.execute("select era,can_apply from authority where scope=0").fetchone()
        permit=db.execute("select payload from permit where intent=?",(station.KEY,)).fetchone()
        ready=(right==(1,0) and permit==(station.journal.encode(station.PAYLOAD),)
               and station.tag(db)==digest)
    # Exact report destination is an independent fixture configuration fact.
    cap,_,_,loc,*_=case['case']
    att,obs=parse(case['tape'],cap,{'Base:7':'Base','alt:7':'Ingress','Far:7':'Far',
                                   'sample:7':'Base' if loc==1 else 'Verifier'})
    scope='station/'+station.KEY
    data=[Event(1,F(0),scope,'fence',None,digest)]
    body=digest+'r'*(173-len(digest))
    for c in obs.values():
        if c.endpoint!={'P':'Base:7','Q':'alt:7'}.get(c.sender) or c.size!=173:
            continue
        a=att[c.attempt]
        data.append(Event(a.proof+1,a.time,scope,'attempt',1,digest,a.charged==c.size))
        content=c.body[:64]
        data.append(Event(c.proof+1,c.time,scope,'arrival',a.proof+1,
                          content,ready and c.body==body))
    data.sort(key=lambda x:x.seq)
    got=first(data,Contract(scope,('fence','attempt','arrival'),1,F(5,4),digest))
    if got is not None:
        assert station.install(new,digest,True)
    out=station.run(new,2)
    assert out==case['case_result']
    assert (got-1 if got else None)==(case['hit'][0] if case['hit'] else None)
    assert station.run(old,1)=={'status':'refused'}
    # Independent direct condition consuming exactly the same facts.
    direct=ready and any(c.time<=F(5,4) and c.body==body and
                         c.endpoint=={'P':'Base:7','Q':'alt:7'}.get(c.sender)
                         for c in obs.values())
    assert direct==(got is not None)
    return dict(case=case['case'],authorization=ready,eligibility=got,outcome=out)

def main(up):
    station=read_owner(up)
    ans=[]
    for row in json.loads((up/'captured.json').read_text()):
        with TemporaryDirectory() as root:
            ans.append(go(station,row,Path(root)))
    return ans
if __name__=='__main__':
    print(json.dumps(main(Path(sys.argv[1])),sort_keys=True))
