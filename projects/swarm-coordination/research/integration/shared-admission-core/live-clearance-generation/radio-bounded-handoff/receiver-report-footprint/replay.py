"""Check the timed, authorized closing of a diagnostic-only receiver."""
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess
import sys

import types

def read_owner(up):
    path=up/'owner.py'
    src=path.read_text()
    marker='\nif len(sys.argv)>2 and sys.argv[2]=="fencer":' 
    assert src.count(marker)==1
    mod=types.ModuleType("owner")
    mod.__file__=str(path)
    exec(compile(src.split(marker)[0],str(path),'exec'),mod.__dict__)
    return mod

owner=read_owner(Path(sys.argv[1]))

def oracle(case):
    cap,pt,rx,loc,reserve,z,arm=case
    reported=(rx+173+(z if arm==2 and reserve else 0)<=cap)
    read=1+int(reported) if loc and rx+z<=cap else 0
    post=rx+(z if loc==1 and read else 0)
    p=(pt+173<=cap) and ((post+173<=cap) if arm==0 else read==2 if arm in (1,2) else False)
    old=1 if p and post+173<=cap else 0 if p else 2
    extra=int(p)
    return pt,rx,post,173*(old==2),160 if p else 173,old,extra,read,int(p)

def execute(binary,body,cases):
    r=subprocess.run([binary,body],input=''.join(' '.join(map(str,c))+'\n' for c in cases),
                     capture_output=True,text=True,check=True)
    t=[]
    for case,line in zip(cases,r.stdout.splitlines(),strict=True):
        *values,pkt=line.split()
        values=tuple(map(int,values))
        assert values==oracle(case),(case,values,oracle(case))
        assert pkt==(body if values[5] else '-')
        t.append((values,pkt))
    return t

def owner_case(root,cpp,case):
    old,new=root/'old.sqlite',root/'new.sqlite'
    owner.init(old,True)
    assert owner.run(old,1,'after-commit',True)=={'status':'silent'}
    digest=owner.fence(old)
    owner.transfer(old,new)
    body=digest+('r'*(173-len(digest)))
    [(values,payload)]=execute(cpp,body,[case])
    if payload=='-':
        assert not owner.install(new,None,True)
        result=owner.run(new,2)
        assert result=={'status':'refused'}
    else:
        assert owner.install(new,payload[:64],True)
        result=owner.run(new,2)
        assert result=={'status':'cached','tick':8,'result':[1,0]}
    assert owner.run(old,1)=={'status':'refused'}
    return dict(case=case,wire=values,native=result)

def main():
    cpp=sys.argv[2]
    cases=list(product((319,320,321),(0,140,147,148),(0,139,146,147,148,310,320),
                       (0,1,2),(0,1),(1,8),(0,1,2,3)))
    cases=[c for c in cases if c[2]<=c[0]]
    output=execute(cpp,'x'*173,cases)
    # Monotonic guarantee for a live, faithfully scoped envelope.
    for c,(v,_) in zip(cases,output):
        if c[-1]==2 and (not c[3]==1 or c[4]):
            assert v[5]!=0
    selected=[]
    for case in product((320,),(140,),(147,),(1,2),(0,1),(1,),(0,1,2,3)):
        with TemporaryDirectory() as d:
            selected.append(owner_case(Path(d),cpp,case))
    print(json.dumps(dict(broker_cases=len(cases),native=selected),sort_keys=True))
if __name__=='__main__':main()
