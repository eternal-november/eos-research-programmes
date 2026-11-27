"""Check the timed, authorized closing of a diagnostic-only receiver."""
from contextlib import closing
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

def oracle(cap,prior,n,early,fanout,deadline,arm):
    # Independent finite model: walk the pending send's live listeners;
    # capacity bounds attempted TX even if none of them decodes.
    sent=prior
    for _ in range(int(not early)+int(fanout)):
        if sent+n<=cap: sent+=n
    active=sent if deadline<=1.25 else 0
    p_active=active
    q_active=4 if deadline<=1.25 else 0
    if arm==5:
        # Both attempts are submitted before the cutoff. The backup charges
        # even if the receiver window has already accepted the primary.
        assert 173+q_active<=cap<2*173
        p=int(active+173<=cap)
        return prior,sent,active+173*p,173,2,1,1,int(fanout),(1 if p else 2),0,q_active+173,2
    if arm:
        # Enumerate both eligible destinations of the preinstalled digest.
        # Compare first preserving old service, then maximizing side bytes.
        options={}
        for s,debit in [('P',active),('Q',q_active)]:
            old=int(debit+173<=cap)
            extra=int(q_active+(173*old if s=='Q' else 0)+160<=cap)
            options[s]=old,extra
        choice={1:'Q',3:'P'}.get(arm)
        if choice is None:
            choice=max(options,key=lambda x:(options[x],x=='P'))
        o,e=options[choice]
        return (prior,sent,(active+173*o if choice=='P' else sent),173*o,
                        2,1,o,int(fanout),1 if choice=='P' else 2,e,
                        q_active+173*o*(choice=='Q')+160*e,1+int(arm==4 and choice=='Q'))
    ok=active+173<=cap
    # The native attempt purges expired entries before accumulating.
    return prior,sent,active+173*ok,173*ok,2,1,int(ok),int(fanout),1,0,4,1

def execute(binary,body,cases):
    inp=''.join(' '.join(str(int(v) if isinstance(v,bool) else v)
                        for v in row)+'\n' for row in cases)
    res=subprocess.run([binary,body],input=inp,capture_output=True,text=True,check=True)
    xs=[]
    for row in res.stdout.splitlines():
        *ints,payload=row.split()
        parsed=tuple(map(int,ints))
        assert payload==(body if parsed[6] else '-')
        xs.append((parsed,payload))
    assert len(xs)==len(cases)
    return xs

def probe(cap,prior,n,early,fanout,deadline,arm=0):
    return (cap,prior,n,early,fanout,deadline,arm)

def native_owner(root,binary,case):
    # Old duty is an exact keyed cached result; the sender can disclose an
    # existing fenced digest, never a privileged oracle about future delivery.
    old,new=root/'old.sqlite',root/'new.sqlite'
    owner.init(old,True)
    assert owner.run(old,1,'after-commit',True)=={'status':'silent'}
    digest=owner.fence(old)
    owner.transfer(old,new)
    body=digest+('r'*(173-len(digest)))
    [(measured,payload)]=execute(binary,body,[case])
    assert measured==oracle(*case)
    if payload=='-':
        assert not owner.install(new,None,True)
        result=owner.run(new,2)
        assert result=={'status':'refused'}
    else:
        assert owner.install(new,payload[:64],True)
        result=owner.run(new,2)
        assert result=={'status':'cached','tick':8,'result':[1,0]}
    assert owner.run(old,1)=={'status':'refused'}
    side=owner.journal.iso.make(owner.journal.n,False)
    owner.journal.n.step(side,[owner.A.NOOP.value,owner.A.FORWARD.value])
    assert (side.agents[1].x,side.agents[1].y)==(2,1)
    return dict(case=case,measure=measured,old=result,side_xy=[2,1])

def main():
    cpp=sys.argv[2]
    cases=list(product((172,173,200,319,320,321,329),
                       (0,25,139,140,146,147), (1,7,8,32),
                       (False,True),(False,True),(1.,1.25,1.2501),(0,)))
    rs=execute(cpp,'x'*173,cases)
    for case,(meas,_) in zip(cases,rs):
        expect=oracle(*case)
        assert meas==expect,(case,meas,expect)
    selected=[probe(cap,140,8,early,fanout,deadline) for cap,early,fanout,deadline in
              product((320,321),(False,True),(False,True),(1.25,1.2501))]
    ns=[]
    for case in selected:
        with TemporaryDirectory() as path:
            ns.append(native_owner(Path(path),cpp,case))
    agree=[]
    for cap,early,fanout,deadline,arm in product((320,321),(False,True),(False,True),
                                                  (1.25,1.2501),(1,2,3,4,5)):
        case=probe(cap,140,8,early,fanout,deadline,arm)
        with TemporaryDirectory() as path:
            agree.append(native_owner(Path(path),cpp,case))
    by={(tuple(x['case'][:-1]),x['case'][-1]):x for x in agree}
    for case,arm in list(by):
        if arm==2:
            a,b=by[case,2]['measure'],by[case,4]['measure']
            assert a[:-1]==b[:-1] and a[-1]<=b[-1]
            c=by[case,5]['measure']
            assert c[6]==a[6]==1 and not c[9] and c[10]>=a[10]-160
    print(json.dumps(dict(native_cases=len(cases),native_station=ns,adaptive=agree),
                     sort_keys=True))
if __name__=='__main__': main()
