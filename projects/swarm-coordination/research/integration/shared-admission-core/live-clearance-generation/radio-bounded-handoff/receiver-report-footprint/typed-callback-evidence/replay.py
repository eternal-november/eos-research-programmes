"""Check exact callback ancestry and consumption from a native source cut."""
import sys,json,subprocess,types,sqlite3
from fractions import Fraction
from contextlib import closing
from pathlib import Path
from tempfile import TemporaryDirectory
from itertools import product
from trace import parse,typed_consume

def read_owner():
    p=Path(sys.argv[1])/'owner.py'
    marker='\nif len(sys.argv)>2 and sys.argv[2]=="fencer":'
    s=p.read_text()
    assert s.count(marker)==1
    ns=types.ModuleType('owner')
    ns.__file__=str(p)
    exec(compile(s.split(marker)[0],str(p),'exec'),ns.__dict__)
    return ns
owner=read_owner()

def modify(e,i,value):
    y=e.split();y[i]=str(value)
    return ' '.join(y)

def negative(raw,cap,b,parsed):
    rejected=0
    # Do not test denial of service against a deployment. These controls
    # simply violate hypotheses in the generated, local evidence checker.
    for k,c in parsed.items():
        for variant in (modify(raw[k-1],3,'Other'),modify(raw[k-1],1,'2'), modify(raw[k-1],4,'Far:7')):
            if variant==raw[k-1]:continue
            tape=list(raw);tape[k-1]=variant
            try:parse(tape,cap,b)
            except ValueError:rejected+=1
            else:raise AssertionError('misbound proof accepted')
    return rejected

def go(root,case,stale):
    cap,pt,rx,loc,reserve,z,arm=case
    old,new=root/'old.sqlite',root/'receiver.sqlite'
    owner.init(old,True)
    assert owner.run(old,1,'after-commit',True)=={'status':'silent'}
    if stale:
        owner.transfer(old,new)
    tag=owner.fence(old)
    if not stale:
        owner.transfer(old,new)
    body=tag+'r'*(173-len(tag))
    p=subprocess.run([sys.argv[2],body],input=' '.join(map(str,case))+'\n',
                     capture_output=True,text=True,check=True)
    lines=p.stdout.splitlines()
    tape=lines[:-1]
    *summary,payload=lines[-1].split()
    known={"Base:7":"Base","alt:7":"Ingress","Far:7":"Far","sample:7":("Base" if loc==1 else "Verifier")}
    attempts,callbacks=parse(tape,cap,known)
    with closing(sqlite3.connect(new.resolve().as_uri()+'?mode=ro',uri=True)) as rd:
        rd.execute('begin')
        right=rd.execute("select era,can_apply from authority where scope=0").fetchone()
        permit=rd.execute("select payload from permit where intent=?",(owner.KEY,)).fetchone()
        coherent=(right==(1,0) and permit==(owner.journal.encode(owner.PAYLOAD),)
                  and owner.tag(rd)==tag)
    assert coherent==(not stale)
    hit=typed_consume(callbacks,attempts,tag,coherent)
    assert bool(hit)==(payload!='-' and coherent)
    assert typed_consume(callbacks,attempts,tag,coherent,Fraction(1)) is None
    assert typed_consume(callbacks,attempts,tag,False) is None
    assert typed_consume(callbacks,attempts,'z'*64,True) is None
    if hit:
        assert owner.install(new,callbacks[hit[0]].body[:64],True)
    else:assert not owner.install(new,None,True)
    result=owner.run(new,2)
    assert result==({'status':'cached','tick':8,'result':[1,0]} if hit else {'status':'refused'})
    return dict(tape=tape,case=case,stale=stale,hit=hit,case_result=result,rejected=negative(tape,cap,known,callbacks))

def main():
    expected=[]
    for cap,pt,rx,loc,reserve,z,arm,stale in product((320,),(140,),(147,),(1,2),(0,1),(1,),(1,2),(0,1)):
        with TemporaryDirectory() as path:
            expected.append(go(Path(path),(cap,pt,rx,loc,reserve,z,arm),bool(stale)))
    idx={(tuple(x['case']),x['stale']):x for x in expected}
    for case,stale in idx:
        good,bad=idx[case,False],idx[case,True]
        assert good['tape']==bad['tape']
        assert bad['hit'] is None
    shared=idx[(320,140,147,1,0,1,1),False]
    separate=idx[(320,140,147,2,0,1,1),False]
    early=lambda x:[line for line in x['tape']
                    if line.startswith('callback ') and Fraction(line.split()[2])<1]
    assert early(shared)==early(separate)
    assert shared['hit'] is None and separate['hit'] is not None
    assert any(l.startswith("attempt ") and " Reporter Base 1 " in l for l in shared['tape'])
    assert any(l.startswith("attempt ") and " Reporter Verifier 1 " in l for l in separate['tape'])
    print(json.dumps(expected,sort_keys=True))
if __name__=='__main__':main()
